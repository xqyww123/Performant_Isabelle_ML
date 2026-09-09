(*  Title:  library/accounted_timeout.ML
    Author: Qiyuan Xu (with AI assistance)

Timeout.apply that claims the Exn.Interrupt_Breakdown its own timer caused.

THE DEFECT (Isabelle2025-2; Pure is NOT patched).  A thread interrupt is a
Poly/ML request plus a per-thread "break" flag saying "this one is ours"
(isabelle_thread.ML:45,145-147).  Delivered with the flag set it surfaces as
Exn.Interrupt_Break, a proper interrupt; delivered with the flag clear it
surfaces as Exn.Interrupt_Breakdown, which Pure treats as an ordinary
exception: Timeout.apply claims only proper interrupts (timeout.ML:50-52) and
releases a Breakdown unchanged (timeout.ML:56).  The flag is lost in
Isabelle_Thread.expose_interrupt_result (isabelle_thread.ML:172-175): it
probes the pending request, then clears the flag unconditionally, so a
cancellation landing between probe and clear is delivered flagless at the
next interruptible point.  Nested Timeout.apply under the scheduler's
re-cancellation every 50 ms (future.ML:161,337-343) makes this ordinary.

THE REMEDY.  Register a witness Event_Timer request beside Timeout.apply's
own -- same physical flag, same expiry formula (timeout.ML:42), empty
callback.  `not (Event_Timer.cancel request)` after the body is exactly how
Timeout.apply decides `was_timeout` (timeout.ML:48): same virtual clock, same
Event_Timer.state lock (event_timer.ML:109,158-171), same GC deferral of
non-physical timers (event_timer.ML:79-82).  A Breakdown surfacing after the
witness fired is that timer's own interrupt with its flag lost, and becomes
Timeout.TIMEOUT.  A Breakdown surfacing before the witness fired is not ours
and is re-raised unchanged, so genuine resource failures keep their shape.

THE SHADOW.  This file ends by rebinding `structure Timeout` with `apply` and
`apply_physical` replaced -- the idiom of isabelle_thread.ML:194,
`structure Exn = Isabelle_Thread.Exn`.  Every ML compiled below
Performant_Isabelle_ML that writes Timeout.apply gets the accounted version;
Accounted_Timeout.raw_apply / raw_apply_physical are the greppable escape to
the original.  The signature stays TIMEOUT verbatim.

RESIDUALS (accepted): a Breakdown landing after Timeout.apply has
returned is out of reach; when nested timers both fire the inner claims and
the outer request is consumed (Timeout.apply's own semantics, timeout.ML:54);
a genuine resource failure AFTER the witness fired is reported as TIMEOUT.
*)


(*** the interrupt family across Par_Exn containers ***)

(*Par_Exn is a container, not a failure: Par_Exn.make filters proper
  interrupts (par_exn.ML:27), but Exn.Interrupt_Breakdown is not proper and
  can sit inside one while Exn.is_interrupt of the container is false.  Test
  per component, ONE level deep (a nested container is an interrupt of a
  nested join, not of the caller); a cancellation surfacing from a body that
  forks internally is otherwise misread as a crash.*)

signature INTERRUPT_FAMILY =
sig
  val find_interrupt: exn -> exn option
  val contains_interrupt: exn -> bool
  val all_breakdown: exn -> bool
end

structure Interrupt_Family: INTERRUPT_FAMILY =
struct

fun find_interrupt exn =
  if Exn.is_interrupt exn then SOME exn
  else
    (case Par_Exn.dest exn of
      SOME exns => find_first Exn.is_interrupt exns
    | NONE => NONE)

val contains_interrupt = is_some o find_interrupt

(*NON-EMPTY: Par_Exn.dest of a proper interrupt is SOME [] (par_exn.ML:36),
  which must not pass as vacuously all-Breakdown*)
fun all_breakdown exn =
  Exn.is_interrupt_breakdown exn orelse
    (case Par_Exn.dest exn of
      SOME (exns as _ :: _) => forall Exn.is_interrupt_breakdown exns
    | _ => false)

end


(*** the accounted timeout ***)

signature ACCOUNTED_TIMEOUT =
sig
  val raw_apply: Time.time -> ('a -> 'b) -> 'a -> 'b
  val raw_apply_physical: Time.time -> ('a -> 'b) -> 'a -> 'b
  val apply: Time.time -> ('a -> 'b) -> 'a -> 'b
  val apply_physical: Time.time -> ('a -> 'b) -> 'a -> 'b
end

structure Accounted_Timeout: ACCOUNTED_TIMEOUT =
struct

(*bound before the shadow below: the originals*)
val raw_apply = Timeout.apply
val raw_apply_physical = Timeout.apply_physical

fun raw true = raw_apply_physical
  | raw false = raw_apply

(*Three disciplines, each load-bearing (precedent: race.ML, event_log.ML):
  (a) uninterruptible_body + Exn.capture0, never a bare `handle`: the handler
      would run under the caller's interruptible attributes, and restoring
      attributes performs a testInterrupt (thread_attributes.ML:57-58) that
      displaces the exception in flight.  capture0, not capture: the managed
      capture consumes the break flag through check_interrupt, i.e. the very
      probe-then-clear this file exists to compensate for.
  (b) never \<^try> ... catch: Isabelle_Thread.try_catch re-raises the whole
      interrupt family, Breakdown included, before any handler runs.
  (c) the witness is cancelled exactly once, on every exit: a second cancel
      finds nothing and returns false, which reads as "fired".*)
fun apply' physical timeout f x =
  if Timeout.ignored timeout then raw physical timeout f x   (*mirror timeout.ML:34*)
  else
    Thread_Attributes.uninterruptible_body (fn run =>
      let
        val start = Time.now ()
        val request =
          Event_Timer.request {physical = physical} (start + Timeout.scale_time timeout)
            (fn () => ())
        val result = Exn.capture0 (fn () => run (raw physical timeout f) x) ()
        val fired = not (Event_Timer.cancel request)
      in
        (case result of
          Exn.Res y => y
        | Exn.Exn exn =>
            if fired andalso Interrupt_Family.all_breakdown exn
            then
              raise Timeout.TIMEOUT (Time.now () - start)
            else Exn.reraise exn)
      end)

fun apply timeout f x = apply' false timeout f x
fun apply_physical timeout f x = apply' true timeout f x

end


(*** the shadow: from here on, Timeout.apply is the accounted version ***)

structure Timeout: TIMEOUT =
struct
  open Timeout
  val apply = Accounted_Timeout.apply
  val apply_physical = Accounted_Timeout.apply_physical
end

(*TEMPORARY hunt marker (`exception Option`, 2026-09-03): forces this session to
  rebuild so its ROOT ML_debugger option takes effect (a ROOT options change alone
  does not enter the session digest).  Delete with the hunt.*)
