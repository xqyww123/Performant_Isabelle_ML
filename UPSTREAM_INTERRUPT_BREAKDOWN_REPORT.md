# Draft upstream report: `Exn.Interrupt_Breakdown` from a lost break flag

Status: DRAFT for the author's review (INTERRUPT_BREAKDOWN_PLAN.md, section 4.6).
Every line number below refers to **Isabelle2025-2** as distributed, re-checked
on 2026-08-31.  Signature and channel (isabelle-dev / private mail to the
maintainer) are the author's decision.

## Summary

A thread's cancellation can be delivered as `Exn.Interrupt_Breakdown` although it
was a perfectly ordinary, properly accounted cancellation.  The cause is that the
per-thread "break" record is a *boolean* that is read-and-cleared without any
atomicity against the code that sets it: `Isabelle_Thread.expose_interrupt_result`
first probes for a pending interrupt request and then clears the record
unconditionally, so a cancellation that arrives between the probe and the clear
loses its record and surfaces later as `Interrupt_Breakdown`.  Since Pure treats
`Interrupt_Breakdown` as an ordinary exception in at least three places, the
lost cancellation then shows up as a failure (a timeout that is not reported as
`Timeout.TIMEOUT`, a `Par_Exn` carrying an "error", a permanently poisoned
`Lazy`), and in one situation it can even displace the body's real exception.

We observe this routinely in a system that nests `Timeout.apply` on worker
threads (the outer timer's cancellation lands in the epilogue of an inner
`Timeout.apply`); the scheduler's re-cancellation of cancelled groups every
50 ms makes the window easy to hit.

## The mechanism

`Pure/Concurrent/isabelle_thread.ML`:

- the record: `break: bool Synchronized.var` per thread (line 45);
- `interrupt_thread` (145-147): posts the Poly/ML request, then sets the record
  to `true` -- in that order, under the record's own lock;
- `reset_interrupt` (149-150): reads the record and sets it to `false`;
- `make_interrupt` (152): `true` -> `Interrupt_Break`, `false` -> `Interrupt_Breakdown`;
- `check_interrupt` (154-155): a raw `Thread.Interrupt` is classified by
  `reset_interrupt`;
- `expose_interrupt_result` (167-176): probes with `Thread.testInterrupt` under
  `test_interrupts` (172), restores the attributes (173), then calls
  `reset_interrupt` **unconditionally** (175); if the probe found nothing, the
  value read from the record is **discarded** (176).

Minimal interleaving.  Thread A is finishing a `Timeout.apply`
(`Pure/Concurrent/timeout.ML`); thread B cancels A (an outer `Timeout.apply`'s
`Event_Timer` callback, or the scheduler's `cancel_now`).

1. A: the body has returned; A cancels its own timer (`timeout.ML:48`).
2. A: `expose_interrupt_result`: `testInterrupt` finds no request; `test = Res ()` (`:172`).
3. B: `interrupt_thread A`: posts the request, sets A's record to `true` (`:145-147`).
4. A: restores its attributes (`:173`) -- still `no_interrupts` inside
   `Timeout.apply` (`timeout.ML:36`), so nothing is delivered.
5. A: `reset_interrupt` reads `true`, writes `false` (`:175`).
6. A: `test` is not an interrupt, so the value read in step 5 is dropped (`:176`).
7. A: `Timeout.apply` sees neither a proper interrupt in `result` nor in `test`
   (`timeout.ML:50-52`) and returns normally (`:56`).
8. A: `Thread_Attributes.with_attributes` restores the caller's asynchronous
   attributes; `set_attributes` performs `testInterrupt`
   (`Pure/Concurrent/thread_attributes.ML:57-58`) and the request posted in
   step 3 is delivered as a raw `Thread.Interrupt`.
9. A: the nearest managed capture classifies it through `check_interrupt`
   (`:154`): the record is `false` -> `Exn.Interrupt_Breakdown`.

B's cancellation was correct and accounted; it is reported as a breakdown.

A second, rarer source with the same root: two cancellations of one thread in
quick succession are folded into one boolean.  When the first delivery has been
taken by Poly/ML but its `reset_interrupt` has not yet run, a second
`interrupt_thread` re-posts the request and sets the (already true) record; the
first delivery's `reset_interrupt` then consumes the single record, and the second
delivery surfaces as `Interrupt_Breakdown`.

Amplifier: `Pure/Concurrent/future.ML` re-cancels every not-yet-dead cancelled
group each scheduler round (`next_round = seconds 0.05`, line 161; the
"canceled groups" step at 337-343), and the threads of such a group are
typically running the epilogues of nested `Timeout.apply`s.  The probe-then-
clear window exists at four sites: `timeout.ML:49`, `future.ML:217`
(`interruptible_task`), `future.ML:237` (`worker_exec` finish), and
`Pure/PIDE/command.ML:228`.

Note that a thread's *own* `Timeout.apply` timer cannot fall into its own
window: `Event_Timer.cancel` and the callback are serialised by
`Event_Timer.state` (`Pure/Concurrent/event_timer.ML:109,158-171`).  Only a
foreign canceller can.  This matches what we measure: every observed
`Interrupt_Breakdown` sits on a thread of a group that has just been cancelled,
or under an outer `Timeout.apply` whose timer fired during an inner epilogue.

## Where Pure then treats the lost cancellation as a failure

`Exn.is_interrupt_proper` (raw or `Interrupt_Break`) versus `Exn.is_interrupt`
(proper or `Interrupt_Breakdown`), `Pure/General/exn.ML:110-117`.  Three places
use the proper test where the consequence is that a breakdown is handled as an
ordinary error:

1. `timeout.ML:50-52`: `was_interrupt` only tests proper.  An outer
   `Timeout.apply` whose own timer fired, but whose cancellation surfaced as
   `Interrupt_Breakdown`, does **not** raise `Timeout.TIMEOUT`; the breakdown is
   released as an ordinary exception (`:56`).  For us this is the symptom that
   reaches the user: a replay budget expires and the proof step fails with
   "Interrupt_Breakdown" instead of a timeout.
2. `Pure/Concurrent/par_exn.ML:23-24,27`: `par_exns` filters only proper
   interrupts, so a breakdown is wrapped into `Par_Exn` as if it were a failure
   (the container's invariant, line 24, is stated in terms of proper interrupts),
   and `release_first` (50-52) re-raises it as the first "plain" exception.  A
   batch of tasks that were *all* merely cancelled is reported as a crash.
3. `Pure/Concurrent/lazy.ML:108`: only a proper interrupt resets a `Lazy`; a
   breakdown is memoised forever.

Two further consequences of the same root, at the task boundary:

- A foreign cancellation that lands after `worker_exec`'s finish drain
  (`future.ML:237`) leaves the record set on a worker that is about to pick up
  the next task; that task then receives a *proper* interrupt it never asked for.
- When `worker_exec` nests (a joining thread executing a queued task), the inner
  finish drain consumes the outer task's cancellation.

And an ordering issue in the epilogue itself: `timeout.ML:56` releases `test`
before `result`, so a breakdown manufactured by the epilogue's own probe displaces
the exception the body actually raised.

## Suggested fix (in Pure)

Make the probe and the clear one atomic step under the record's lock, or clear
the record only when the probe actually took an interrupt:

```sml
fun expose_interrupt_result () =
  let
    val orig_atts = Thread_Attributes.safe_interrupts (Thread_Attributes.get_attributes ());
    fun main () =
      (Thread_Attributes.set_attributes Thread_Attributes.test_interrupts;
       Thread.Thread.testInterrupt ());
    val test = Exn.capture0 main ();
    val _ = Thread_Attributes.set_attributes orig_atts;
  in
    if Exn.is_interrupt_exn test then Exn.Exn (make_interrupt (reset_interrupt ()))
    else test
  end;
```

With this, a cancellation posted after the probe keeps its record and is
classified correctly at delivery.  The boolean folding of two cancellations would
remain; a counter, or recording the source, would close that too.

Independently of the above, `Timeout.apply` could claim `Interrupt_Breakdown` as
its own timeout when its timer has fired (`was_timeout andalso Exn.is_interrupt_exn
...`), which is what we do downstream in the meantime: a wrapper registers a
witness `Event_Timer` request beside `Timeout.apply`'s own and converts a
breakdown that surfaces after the witness fired into `Timeout.TIMEOUT`.

## How we observe it

The system nests `Timeout.apply` on worker threads (a replay budget around a
sequence of proof steps, each step under its own `Timeout.apply`) and runs races
whose losers are cancelled by group.  Under Isabelle2025-2 we log every
`Interrupt_Breakdown` at the site that first sees it.  In the run used for this
report, 18 records were collected, every one on a thread of a group that had just
been cancelled (a race loser); a separate full evaluation logged 5 within its
first ten minutes.  One path -- the replay budget expiring inside an inner
epilogue -- reaches the user as a spurious "Interrupt_Breakdown" error on a
proof step.  (Counts to be refreshed by the author before submission.)
