(* A parallel race: run competing thunks, return the first decisive result, and
   report honestly how every competitor ended.

   A racer is a named thunk returning SOME on a decisive result, NONE otherwise.
   `race` runs all racers and returns
     - winner : the decisive result, named after the racer that produced it;
     - exits  : one exit per input racer, in input order;
     - forked : whether the racers actually ran in parallel.

   THE CONTRACT.

   * The first decisive result to arrive ends the race: the racer records its
     claim and all other racers are cancelled promptly (forked mode: the group
     holding the racers is cancelled, which interrupts running bodies and kills
     queued ones before they start; serial mode: later racers are simply never
     started -- and, since serial mode has no group and runs every racer on
     the caller's thread, a serial racer's internal interrupt re-raises out of
     `race` instead of ending that racer alone: consistent with the
     attribution rule below, but without forked mode's isolation).  When
     several claims arrive concurrently, the lowest input index
     wins -- each racer records its claim under deferred interrupts, so a
     decisive result that has been computed is always recorded -- but which
     claims arrive at all is a scheduling fact, not a promise.  There is no
     internal degradation to a non-short-circuiting map: the parallel-or-serial
     decision is taken ONCE, at entry, by the same relevance test
     `Future.relevant` uses, and `forked` reports that decision truthfully.
     This is the reason this module exists instead of `Par_List.get_some`,
     which can silently degrade to `map (Exn.capture f)` and then lets losers
     burn their full budgets after a winner is known.

   * Exits.  Won        -- the winner (exactly one, iff winner = SOME);
             Gave_None  -- ran to completion, returned NONE;
             Timed_Out  -- body raised Timeout.TIMEOUT;
             Crashed    -- body raised a non-interrupt exception;
             Cancelled  -- interrupted while running, or never started;
             Discarded  -- produced a decisive result whose claim was recorded
                          but lost to a lower input index; carries that result.
                          Cannot occur in serial mode (execution stops at the
                          first decisive result).  A racer that computed SOME
                          but was interrupted before recording its claim
                          reports Cancelled, not Discarded.  A non-claimant
                          can be displaced the same way: a racer finishing as
                          Gave_None, Crashed, or Timed_Out in the instant a
                          claim cancels the field can have that outcome
                          overwritten by the arriving interrupt and report
                          Cancelled -- fails safe, tolerated by design.

   * Join barrier.  On every path -- winner, no winner, exception -- all forked
     racers have terminated before `race` returns: no stray thread survives the
     call, and a racer's side-effect writes (e.g. a `Synchronized.change` into
     a record variable) are visible to the caller as soon as `race` returns.
     Deliberately STRONGER than `Future.forked_results`, which on interrupt
     merely cancels and re-raises without waiting for the group to die.

   OBLIGATIONS ON THE CALLER.

   (a) Racer bodies must be self-bounded (e.g. wrapped in `Timeout.apply`):
       the no-winner path joins every racer, so a single unbounded racer
       blocks the return of the whole race.
   (b) `race` must not be called with interrupts already deferred: the join
       then runs uninterruptibly (`join_results` wraps its waiting in the
       caller's attributes, future.ML:534-536, and the waits keep deferring),
       so an enclosing `Timeout.apply` on the caller cannot cut the join
       short -- the race runs until the racers finish on their own budgets,
       and the caller's interrupt fires only after `race` returns.  The racer
       bodies themselves are unaffected: each job installs its own
       interruptible attributes, fixed at fork time (future.ML:473-475), so
       loser cancellation and the racers' `Timeout.apply` budgets keep
       working, and even absorbed cancellation still lands when a job
       re-enables asynchronous interrupts inside a body executed on the
       joining thread.

   EXCEPTIONS.

   An interrupt is cancellation, never failure: the engine never converts an
   interrupt into a result, and external cancellation re-raises out of `race`
   even when a racer has already claimed -- with the single exception
   recorded as residual (c) below.  A racer body raising a
   non-interrupt exception fails that racer alone (exit Crashed); the race
   continues.  A racer body raising `Timeout.TIMEOUT` gets exit Timed_Out.

   When a racer body surfaces an interrupt, the engine attributes it:
     - the group holding the racers is canceled: this racer was cancelled --
       by another racer's claim, or because the whole race is being cancelled
       through an ancestor group -- exit Cancelled;
     - the interrupt landed on the very thread that called `race` (which, on
       a worker thread, can be executing a still-queued racer body it picked
       up while joining, future.ML:510-543): this is the caller's own
       cancellation, absorbed into a racer; the race is cancelled and the
       interrupt re-raised after the join;
     - otherwise the interrupt came from the racer's own nested machinery
       (e.g. an internal `Future.forked_results` delivering a `Par_Exn` that
       carries `Exn.Interrupt_Breakdown`): that racer alone exits Cancelled
       and the race continues.  This attribution is sound because every
       external cancellation route in Pure either cancels a group before
       interrupting its threads (future.ML:198,204) or targets the caller's
       thread directly (timeout.ML:38,43).

   Three irreducible residuals, all verified against Pure:
     (a) a racer's own internal interrupt that surfaces while the caller is
         executing that racer's body picked up during the join is
         indistinguishable from the caller's absorbed cancellation; the
         engine fails safe and cancels the whole race;
     (b) a foreign interrupt arriving just as a racer's own `Timeout.apply`
         deadline expires is reported as that racer's timeout
         (timeout.ML:47-54): the racer exits Timed_Out and the cancellation
         is consumed;
     (c) when the caller's thread is executing a racer body picked up during
         the join and another racer's claim cancels the field in the same
         instant as the caller's own enclosing `Timeout.apply` fires, the two
         interrupts coalesce on the thread's one break flag: the attribution
         finds the racers' group canceled and returns Cancelled without
         recording the caller's cancellation, the parent group is not
         canceled either, so `race` returns the winner and the enclosing
         timeout never fires -- the caller's cancellation is lost, with a
         result.  This is the opposite direction of residual (a): (a)
         mistakes a racer's internal interrupt for the caller's and
         over-cancels; (c) mistakes the caller's interrupt for the engine's
         own cancellation and under-cancels.  Deliberately not "fixed":
         recording the caller's cancellation whenever an interrupt lands on
         the caller's thread, regardless of group state, would let every
         claim that catches a body executing on the joining thread abort a
         good race -- a worse false positive traded for a rarer false
         negative.

   GROUPS.

   Two fresh groups are created per race.  The first is a child of the
   caller's worker group; the engine NEVER cancels it, so after the join it
   is an honest probe for external cancellation: if it is canceled, the
   cancellation came from outside (`Task_Queue.cancel_group` mutates only the
   given group's own status, while `Task_Queue.is_canceled` walks the
   ancestor chain upward).  The second, its child, holds ALL racers and is
   what claims and the engine's own cancellations cancel.  All racers are
   forked in one `Future.forks` call at the caller's task priority (the
   parentage and priority discipline of `Future.forked_results`); the worker
   pool schedules them with no concurrency cap.  Called OFF a worker thread,
   the two groups have no ancestor tie to any task and joining merely awaits
   the results without executing tasks (future.ML:538-540), so absorbed
   cancellation is structurally impossible there and an interrupt during the
   join -- the exception path -- is the only external-cancellation route.

   UNINTERRUPTIBLE WINDOWS (each is load-bearing):
   - around fork + join dispatch: an interrupt between forking and installing
     the cancel-on-interrupt handler would orphan the racers;
   - in a racer, everything except the body call itself: classifying the
     outcome and recording a claim must not be robbed by a concurrent
     cancellation;
   - around the exception-path re-join: the join barrier must not itself be
     interruptible, or repeated interrupts would leak racer threads.  That
     re-join terminates because the group holding the racers is already
     cancelled -- unless a racer body swallows interrupts, which hangs
     `Future.join` the same way.
*)

signature RACE =
sig
  type 'a racer = string * (unit -> 'a option)
  datatype 'a exit =
    Won | Gave_None | Timed_Out | Crashed of exn | Cancelled | Discarded of 'a
  val contains_interrupt: exn -> bool
  val race: 'a racer list ->
    {winner: (string * 'a) option,
     exits: (string * 'a exit) list,  (*same order as the input list*)
     forked: bool}
end

structure Race : RACE =
struct

type 'a racer = string * (unit -> 'a option)

datatype 'a exit =
  Won | Gave_None | Timed_Out | Crashed of exn | Cancelled | Discarded of 'a

(*Par_Exn is a container, not a failure: proper interrupts never sit inside one
  (Par_Exn.make filters them), but Exn.Interrupt_Breakdown is NOT proper and
  can -- while is_interrupt of the container itself is false.  Test per
  component, or a cancellation coming out of a racer that forks internally
  would be misread as a crash.  Exported as an interim home, pending
  extraction to a shared kernel of this recurring idiom.*)
fun contains_interrupt exn =
  Exn.is_interrupt exn orelse
    (case Par_Exn.dest exn of
      SOME exns => exists Exn.is_interrupt exns
    | NONE => false)

(*breakdown attribution (EVENT_LOG_PLAN 7): the two branches below where an
  interrupt LEAVES the race are record points -- a breakdown has no raise
  position, so its diagnostic value is the first site that sees it; proper
  cancellations are the engine working as designed and are not logged*)
fun log_escaping site name =
  Exception_Log.record_breakdown (site ^ " escaping, racer=" ^ name)


(** serial mode: run in list order, stop at the first decisive result **)

fun race_serial (racers: 'a racer list) =
  let
    fun go [] exits = {winner = NONE, exits = rev exits, forked = false}
      | go ((name, body) :: rest) exits =
          (case Exn.capture_body body of
            Exn.Res NONE => go rest ((name, Gave_None) :: exits)
          | Exn.Res (SOME x) =>
              {winner = SOME (name, x),
               exits = rev ((name, Won) :: exits) @ map (fn (n, _) => (n, Cancelled)) rest,
               forked = false}
          | Exn.Exn (Timeout.TIMEOUT _) => go rest ((name, Timed_Out) :: exits)
          | Exn.Exn exn =>
              (if contains_interrupt exn
               then (log_escaping "Race.serial" name exn;
                     Exn.reraise exn)
               else go rest ((name, Crashed exn) :: exits)))
  in go racers [] end


(** forked mode **)

fun race_forked (racers: 'a racer list) =
  Thread_Attributes.uninterruptible_body (fn run =>
    let
      val caller = Isabelle_Thread.self ()

      val (parent, pri) =
        (case Future.worker_task () of
          SOME task =>
            (Future.new_group (SOME (Task_Queue.group_of_task task)),
             Task_Queue.pri_of_task task)
        | NONE => (Future.new_group NONE, 0))
      val race_group = Future.new_group (SOME parent)

      (*All claims that arrived, and whether the caller's own cancellation was
        absorbed into a racer.  Claims are recorded here, not read off the
        futures' results: a claimant targeted by a concurrent cancellation can
        have its returned value displaced by the interrupt that fires when its
        job's attributes are restored (future.ML:450-452; the displacing raise
        is thread_attributes.ML:99-101), and the recorded claim is what keeps
        such a racer's Discarded exit truthful.*)
      val state =
        Synchronized.var "Race.state" (([], false): (int * 'a) list * bool)

      (*Only the body itself runs interruptibly (`run` restores the task's
        normal attributes); classifying the outcome and recording a claim run
        under deferred interrupts, so a decisive result that has been computed
        is always recorded.*)
      fun racer_job i (name, body) () =
        Thread_Attributes.uninterruptible_body (fn run =>
          (case Exn.capture_body (fn () => run body ()) of
            Exn.Res NONE => Gave_None
          | Exn.Res (SOME x) =>
              (Synchronized.change state (apfst (cons (i, x)));
               Future.cancel_group race_group;
               Discarded x)
          | Exn.Exn (Timeout.TIMEOUT _) => Timed_Out
          | Exn.Exn exn =>
              (if not (contains_interrupt exn) then
                (*a non-interrupt exception is this racer's failure only and
                  must NOT escape the job: all racers share one group, so an
                  escaping exception would reach assign_result
                  (future.ML:424-436) and cancel the whole field*)
                Crashed exn
              else if Task_Queue.is_canceled race_group then
                (*the race's own machinery cancelled this racer (a claim, or
                  an ancestor group being cancelled); returning -- not
                  re-raising -- keeps assign_result from re-cancelling*)
                Cancelled
              else if Isabelle_Thread.is_self caller then
                (*the caller's thread is executing this racer's body, picked
                  up while joining: an interrupt here is the caller's own
                  cancellation, absorbed.  Record it, take the whole race
                  down, and re-raise.*)
                (Synchronized.change state (apsnd (K true));
                 Future.cancel_group race_group;
                 log_escaping "Race.parallel" name exn;
                 Exn.reraise exn)
              else
                (*not our cancellation, not the caller's thread: provably the
                  racer's own nested machinery (see EXCEPTIONS above) -- this
                  racer's end alone*)
                Cancelled)))

      val futures =
        Future.forks
          {name = "Race.race", group = SOME race_group, deps = [], pri = pri, interrupts = true}
          (map_index (fn (i, r) => racer_job i r) racers)

      (*join barrier: cancellation makes losers finish promptly, so joining ALL
        futures both collects the exits and guarantees that no racer thread
        survives the call.  `run` restores interruptibility for the join only:
        external cancellation lands here, cancels the racers, and re-raises
        after the (uninterruptible) re-join.  Only the group holding the
        racers is cancelled -- never its parent, which must stay an honest
        probe for external cancellation.*)
      val results =
        (case Exn.capture_body (fn () => run Future.join_results futures) of
          Exn.Res results => results
        | Exn.Exn exn =>
            (Future.cancel_group race_group;
             ignore (Future.join_results futures);
             Exn.reraise exn))

      val (claims, externally_cancelled) = Synchronized.value state

      (*External cancellation re-raises even when a racer already claimed:
        the caller's interrupt was consumed on absorption (Isabelle_Thread's
        Exn.capture resets the break flag), so an enclosing Timeout.apply
        would otherwise be silently defeated.  Route one: the never-cancelled
        parent group is canceled, so an ancestor was cancelled from outside.
        Route two: a racer recorded the caller's absorbed cancellation.
        The join barrier already holds here: join_results returned, every
        racer has terminated.  This check MUST precede building the exits: a
        cancelled racer's result may have been rewritten by get_result into a
        Par_Exn over ancestor group status (future.ML:498-506), which can
        carry an unrelated task's non-interrupt exception -- raising here is
        what keeps that case unreachable below.  Do not reorder.*)
      val _ =
        if externally_cancelled orelse Task_Queue.is_canceled parent
        then Isabelle_Thread.raise_interrupt () else ()

      val winner_claim =
        (case claims of
          [] => NONE
        | c :: cs => SOME (fold (fn c' => fn c'' => if #1 c' < #1 c'' then c' else c'') cs c))
      val winner_index = Option.map #1 winner_claim
      val winner = Option.map (fn (i, x) => (#1 (nth racers i), x)) winner_claim

      (*recorded claims are the authority on Won and Discarded (see the note
        at the state variable): for any racer with a recorded claim, the
        Discarded value its job returned is ignored.  Do not "simplify" the
        recorded claims away on the grounds that the job already returns the
        value -- that reintroduces the displacement described there.
        Everything else is read off the results.*)
      val exits =
        map2
          (fn (i, (name, _)) => fn result =>
            (name,
              (case AList.lookup (op =) claims i of
                SOME x => if winner_index = SOME i then Won else Discarded x
              | NONE =>
                  (case result of
                    Exn.Res e => e
                  | Exn.Exn exn =>
                      if contains_interrupt exn then Cancelled else Crashed exn))))
          (map_index I racers) results
    in {winner = winner, exits = exits, forked = true} end)


(*the relevance test is taken ONCE -- the reported mode is the executed mode*)
fun race racers =
  if Future.relevant racers then race_forked racers else race_serial racers

end
