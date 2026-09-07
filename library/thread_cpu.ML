(*  Title:  library/thread_cpu.ML
    Author: Qiyuan Xu (with AI assistance)

The CPU clock of one thread, and a timeout charged in it.

WHY.  Timing.result's cpu is getrusage(RUSAGE_SELF): the whole process, all
workers at once (polyml timing.cpp:468).  A single-threaded computation
running beside other workers cannot be metered by it, and wall clock charges
it for the machine's load and for everybody's garbage collections: Poly/ML's
GC stops the world, and a thread that allocated nothing lost 657 ms of 910 ms
wall to other threads' GCs, none of it on its own CPU clock (measured;
ai-artifacts/THREAD_CPU_MEASUREMENTS.md holds every figure cited here).  The
operating system keeps a CPU clock per thread; this module reads it.

THE MECHANISM.  library/native/thread_cpu.c, three C entry points that are
the same on Linux, macOS and Windows: tc_self yields a process-wide handle to
the CALLING thread's CPU clock, tc_read reads it in nanoseconds, tc_free
releases it.  Because the handle is valid from any thread, one manager thread
can watch every guarded computation, which is what makes `apply' possible.
The C header states the per-platform contract; the parts a caller must know
are in the signature comment below.

The library is libperformant_isabelle_ml, found under
library/native/<platform>/ next to this file, where <platform> is ML_PLATFORM
with a compact-object "_32" stripped from the architecture: Isabelle's stock
default is ML_system_64 = false, so ML_PLATFORM is then x86_64_32-linux while
the directory is x86_64-linux (this machine runs ML_system_64 = true and
reports x86_64-linux directly).  Build it once per machine with
library/native/build <platform> (the conda package ships all five prebuilt;
library/native/README has the details).  It is loaded lazily on first use,
so a heap builds without it; the first use without it raises an error naming
that build command.  There is no wall-clock fallback: a missing library is a
setup error, not a runtime condition.

Foreign itself is hidden by Pure; library/rescue_foreign.ML puts it back and
must precede this file.  Compiled code holds values, not names, so a heap built
from this file works in any later process whether or not the name is bound
there (Isabelle's own SHA1 rests on the same fact, sha1.ML:150-177).  The
dlopen handle and symbol addresses are memoised in volatile refs that Poly/ML
resets on heap load (ForeignMemory.sml:127-135), so nothing stale is baked in.

THE TIMEOUT.  `apply budget f x' runs f x and raises Timeout.TIMEOUT once the
calling thread has spent `budget' of CPU inside it -- the shape of
Timeout.apply (timeout.ML:34-56) with Event_Timer replaced by a manager of our
own.  Event_Timer cannot serve: its event runs inside Event_Timer's own lock,
so it cannot re-arm itself, and a CPU deadline can only be approached by
repeated wall-clock waits.  The manager waits for the smallest remaining
budget among the registrations -- a thread never accrues more CPU than wall
time (except on Windows, where the tick-based clock can credit a thread a
whole 15.625 ms tick it did not fully run), so that wait never runs past a
deadline -- re-reads every clock, fires what is due, and waits again.  Each
wait is at least poll_floor (1 ms) so a starved thread does not turn the
manager into a spinner; a budget therefore overshoots by at most poll_floor
plus scheduling latency, plus one tick on Windows (measured on idle Linux
machines: 22 us to 1.8 ms of CPU beyond a 20 ms budget, over 20 samples).  One
manager thread serves every registration; it is forked on demand and lives on,
exactly as Event_Timer's does, and like Event_Timer's it is revived by the next
register or cancel if found dead (after a heap reload, say).

Firing is Isabelle_Thread.interrupt_thread on the registered thread, and the
outcome is judged as Timeout.apply judges it: TIMEOUT iff the registration
had fired AND a proper interrupt surfaced, from the body or from the flush
(Isabelle_Thread.expose_interrupt_result) afterwards.  In addition, as
accounted_timeout.ML does for Timeout.apply, a Breakdown surfacing after the
registration fired -- from either limb -- is claimed as our interrupt with
its break flag lost; one predicate judges both limbs so they cannot drift.
*)

signature THREAD_CPU =
sig
  (* A thread's CPU clock: the CPU time the operating system has charged to
     that one thread, monotonic, standing still while the thread sleeps,
     blocks, or is stopped by a garbage collection.

     `self' must run ON the thread to be measured and yields a handle to that
     thread's clock.  The handle is valid process-wide: any thread may `read'
     it, which is what lets one thread watch another.  A reading is the
     thread's lifetime total, so an interval is the difference of two readings.
     `free' releases the handle: exactly once, after the last read -- a read
     after `free' reports whatever new thread has been given the handle's
     value (macOS, Windows).

     A clock is meant to be read while its thread lives.  Once the thread is
     gone `read' is NONE on Linux and macOS -- within 6 us of the join on
     Linux, once 0.134 ms later on macOS, whose worst case is not measured --
     and on Windows the final total until `free'.  That is what was observed,
     not a guarantee: the handle is an operating-system name (a clockid
     encoding the thread id, a Mach port name, a Windows handle value), and
     once the system reissues that name a read reports the new owner's total;
     the macOS send right and the Windows handle hold the name until `free',
     on Linux nothing does.  All of this is measured
     (ai-artifacts/THREAD_CPU_MEASUREMENTS.md).

     Resolution: nanoseconds on Linux, microseconds on macOS, and on Windows
     the 15.625 ms scheduler tick -- a Windows budget is meaningful only in
     multiples of that tick.  Time.time itself carries microseconds. *)
  type clock
  val self: unit -> clock
  val read: clock -> Time.time option
  val free: clock -> unit

  (* Run f x; raise Timeout.TIMEOUT (carrying the CPU spent) once the calling
     thread has spent `budget' of its CPU inside it.  Only this thread's CPU
     counts: work in Future/Par_List is invisible, and a blocked thread never
     reaches the budget -- nest inside a wall-clock Timeout.apply where
     liveness matters.

     Budgets are treated as Timeout.apply treats them: under 1 ms the budget
     is ignored and f runs unbounded (Timeout.ignored; also the least this
     manager could honour, since poll_floor is 1 ms), and the timeout_scale
     option scales a CPU budget as it scales a wall-clock one.  The exception
     is Timeout.TIMEOUT itself, so a caller nesting the two clocks cannot tell
     from the exception which fired; only the Time.time differs -- CPU spent
     here, wall elapsed there. *)
  val apply: Time.time -> ('a -> 'b) -> 'a -> 'b
end

structure Thread_CPU: THREAD_CPU =
struct

(** the C library **)

local
  open Foreign

  (*ML_PLATFORM with the compact-object "_32" stripped: the process is still
    64-bit and takes the same library (see the header)*)
  val platform =
    (case space_explode "-" ML_System.platform of
      [arch, os] => perhaps (try (unsuffix "_32")) arch ^ "-" ^ os
    | _ => ML_System.platform)

  val path =
    Resources.master_directory \<^theory> + Path.make ["library", "native", platform,
      if ML_System.platform_is_windows then "performant_isabelle_ml.dll"
      else "libperformant_isabelle_ml.so"]

  val library = loadLibraryIndirect (fn () => File.platform_path path)

  (*the handler sits on the calls, as sha1.ML:193-195 puts it: the library and
    its symbols are memoised thunks and resolve at the first call*)
  fun explain call x =
    call x handle Foreign.Foreign msg =>
      error (msg ^ "\nlibperformant_isabelle_ml could not be loaded from " ^
        File.platform_path path ^ "\nbuild it on this machine with library/native/build " ^ platform)
in
  val tc_self = explain (buildCall0 (getSymbol library "tc_self", (), cInt64))
  val tc_read = explain (buildCall1 (getSymbol library "tc_read", cInt64, cInt64))
  val tc_free = explain (buildCall1 (getSymbol library "tc_free", cInt64, cVoid))
end


(** clocks **)

abstype clock = Clock of int
with

fun self () =
  (case tc_self () of
    0 => error "Thread_CPU.self: the operating system refuses a CPU clock for this thread"
  | h => Clock h)

(*nanoseconds, or NONE once the handle cannot be read*)
fun read_ns (Clock h) = (case tc_read h of ~1 => NONE | ns => SOME ns)

fun free (Clock h) = tc_free h

end

val read = Option.map Time.fromNanoseconds o read_ns

(*only inside apply's no_interrupts scope: the calling thread's own clock,
  freed exactly once, on every exit -- and never before its registration is
  withdrawn, since nothing between `register' and cancel's withdrawal can
  raise.  capture0, not the managed capture: that one consumes the break
  flag through check_interrupt, which apply's flush must still see
  (accounted_timeout.ML)*)
fun with_clock body =
  let
    val clock = self ()
    val result = Exn.capture0 (fn () => body clock) ()
  in free clock; Exn.release result end


(** the manager **)

(*the manager's shortest wait: bounds its wakeups when a guarded thread is
  starved of CPU, and bounds a budget's overshoot*)
val poll_floor = Time.fromMilliseconds 1

(*one guarded computation; deadline: an absolute reading of `clock', in nanoseconds*)
type registration = {clock: clock, deadline: int, thread: Isabelle_Thread.T}

datatype state =
  State of {registrations: registration Inttab.table, manager: Isabelle_Thread.T option}

val state =
  Synchronized.var "Thread_CPU.state" (State {registrations = Inttab.empty, manager = NONE})

(*nanoseconds of budget left; 0 when due, and when the thread is gone*)
fun remaining ({clock, deadline, ...}: registration) =
  (case read_ns clock of
    NONE => 0
  | SOME ns => Int.max (deadline - ns, 0))

(*when to look again: the smallest remaining budget, at least poll_floor away;
  NONE = nothing registered, wait for a change*)
fun wake_time (State {registrations, ...}) =
  Inttab.fold (fn (_, r) => fn w =>
      (case w of
        NONE => SOME (remaining r)
      | SOME w => SOME (Int.min (w, remaining r))))
    registrations NONE
  |> Option.map (fn w =>
      Time.now () + Time.fromNanoseconds (Int.max (w, Time.toNanoseconds poll_floor)))

(*fire one due registration, or NONE = nothing due yet.  The interrupt and the
  entry's removal are ONE critical section of `state' (synchronized.ML:83-86):
  a thread that finds its registration gone knows its interrupt was already
  issued, which is what lets `cancel' report "it had fired" and `apply' trust
  it.  Interrupting outside the lock would break that.*)
fun fire (State {registrations, manager}) =
  (case Inttab.get_first (fn (id, r) => if remaining r = 0 then SOME (id, r) else NONE) registrations of
    NONE => NONE
  | SOME (id, {thread, ...}) =>
      (Isabelle_Thread.interrupt_thread thread;
       SOME ((), State {registrations = Inttab.delete id registrations, manager = manager})))

fun manager_loop () =
  (Synchronized.timed_access state wake_time fire; manager_loop ())

(*event_timer.ML:130-132,163,170*)
fun manager_check manager =
  if is_some manager andalso Isabelle_Thread.is_active (the manager) then manager
  else SOME (Isabelle_Thread.fork (Isabelle_Thread.params "thread_cpu") manager_loop)

val new_id = Counter.make ()

fun register (registration: registration) =
  Synchronized.change_result state (fn State {registrations, manager} =>
    let val id = new_id () in
      (id, State {registrations = Inttab.update (id, registration) registrations,
        manager = manager_check manager})
    end)

(*revive the manager if it died; a separate step because forking can raise*)
fun revive () =
  Synchronized.change state (fn State {registrations, manager} =>
    State {registrations = registrations, manager = manager_check manager})

(*true = still pending (withdrawn now); false = it had fired.  The withdrawal
  itself cannot fail: from here the caller may free the clock*)
fun cancel id =
  Synchronized.change_result state (fn State {registrations, manager} =>
    (Inttab.defined registrations id,
      State {registrations = Inttab.delete_safe id registrations, manager = manager}))
  before revive ()


(** the timeout **)

fun apply budget f x =
  if Timeout.ignored budget then f x
  else
    Thread_Attributes.with_attributes Thread_Attributes.no_interrupts (fn orig_atts =>
      with_clock (fn clock =>
        let
          val start =
            (case read_ns clock of
              SOME ns => ns
            | NONE => error "Thread_CPU.apply: the calling thread's own CPU clock is unreadable")
          val deadline = start + Time.toNanoseconds (Timeout.scale_time budget)
          val id = register {clock = clock, deadline = deadline, thread = Isabelle_Thread.self ()}

          val result =
            Exn.capture_body (fn () => Thread_Attributes.with_attributes orig_atts (fn _ => f x))

          val was_timeout = not (cancel id)
          val stop = read_ns clock
          val test = Isabelle_Thread.expose_interrupt_result ()
          (*our interrupt: proper, or a Breakdown after we fired (the flag-loss case)*)
          fun ours res =
            Exn.is_interrupt_proper_exn res orelse
            (was_timeout andalso
              (case res of Exn.Exn exn => Interrupt_Family.all_breakdown exn | _ => false))
        in
          if was_timeout andalso (ours result orelse ours test)
          then raise Timeout.TIMEOUT (Time.fromNanoseconds (the_default deadline stop - start))
          else (Exn.release test; Exn.release result)
        end))

end
