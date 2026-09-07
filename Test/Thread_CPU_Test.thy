(* Checks for library/thread_cpu.ML: per-thread CPU clocks, Thread_CPU.timing and
   Thread_CPU.apply.

   Run it by hand -- like every other test here, it is deliberately NOT in ROOT.
   Failure is an `error'; success is silence plus the printed measurements.

   Every burn runs until the CLOCK UNDER TEST has advanced by a fixed amount,
   with a wall-clock backstop, so a loaded machine slows the test down instead
   of failing it.  Two kinds of inequality are asserted.  Those that hold under
   any load -- CPU never exceeds wall, a sleeping thread accrues nothing, a
   sample fires at or after its limit -- are the real content.  The upper
   bounds on overshoot (`slack', defined below) assume an idle machine: a failure
   there means the manager was descheduled, not that the clock is wrong.  The
   tolerances are absolute; timeout_scale is checked to be 1, the default, and
   its scaling of a CPU limit is checked on its own below.
   Needs library/native/build <platform> run once on this machine; the
   missing-library fallback is described by the recipe at the end, to be run
   by hand. *)
theory Thread_CPU_Test
  imports "../Performant_Isabelle_ML"
begin

ML \<open>
  fun assert _ true = ()
    | assert msg false = error ("FAILED: " ^ msg)

  (*a stale interrupt would otherwise surface as a bare Interrupt, which reads
    as "somebody cancelled the command"*)
  fun expect_no_interrupt () =
    assert "a stale interrupt was left pending"
      (not (Exn.is_interrupt_exn (Isabelle_Thread.expose_interrupt_result ())))

  fun ms t = string_of_int (Time.toMilliseconds t) ^ " ms"
  fun us t = string_of_int (Time.toMicroseconds t) ^ " us"

  (*the CPU limit alone*)
  fun cpu_apply t = Thread_CPU.apply {thread_cpu = t, wall = NONE}

  val poll_floor = Time.fromMilliseconds 1   (*mirrors poll_floor in library/thread_cpu.ML*)
  (*a reading may lead wall clock by one tick where the clock is coarse (thread_cpu.c)*)
  val tick = if ML_System.platform_is_windows then Time.fromMicroseconds 15625 else Time.zeroTime
  (*the overshoot an idle machine may add to a limit: the manager's own poll
    floor a few times over, plus one tick where the clock is coarse; a failure
    against this bound means the manager was descheduled, not that the clock is
    wrong (see the header)*)
  val slack = Time.scale 10.0 poll_floor + tick
  val _ = assert "the tolerances below assume timeout_scale = 1" (Real.== (Timeout.scale (), 1.0))

  fun reading clock =
    (case Thread_CPU.read clock of
      SOME t => t
    | NONE => error "clock unreadable")

  (*advance `clock' by t, running `step' between readings; the backstop turns a
    clock that never advances into an error rather than a hang*)
  fun advance_on msg clock t step =
    let
      val start = reading clock
      val backstop = Time.now () + Time.scale 30.0 t + Time.fromSeconds 1
      fun loop () =
        if reading clock - start >= t then ()
        else if Time.now () > backstop then error msg
        else (step (); loop ())
    in loop () end

  (*compute-bound: the calling thread burns until `clock' has advanced by t*)
  fun burn_on msg clock t =
    let val x = Unsynchronized.ref 1
    in advance_on msg clock t (fn () => x := (! x * 3 + 1) mod 1000003) end

  (*wait, WITHOUT burning, until `clock' has advanced by t*)
  fun poll_on msg clock t = advance_on msg clock t (fn () => OS.Process.sleep poll_floor)

  (*the same on the calling thread's own clock*)
  fun burn_cpu t =
    let
      val clock = Thread_CPU.the_self ()
      val _ = burn_on "burn_cpu: the thread's own clock did not advance" clock t
    in Thread_CPU.free clock end

  (*compute-bound until interrupted*)
  fun spin () =
    let val x = Unsynchronized.ref 1
    in while true do x := (! x * 3 + 1) mod 1000003; ! x end

  (*an interval on one's own clock: two readings of the same handle*)
  fun own_cpu f x =
    let
      val clock = Thread_CPU.the_self ()
      val t0 = reading clock
      val _ = f x
      val cpu = reading clock - t0
      val _ = Thread_CPU.free clock
    in cpu end
\<close>

section \<open>The clock\<close>

ML \<open>
  val wall0 = Time.now ()
  val cpu = own_cpu burn_cpu (Time.fromMilliseconds 40)
  val wall = Time.now () - wall0
  val _ = writeln ("own clock: burned 40 ms of CPU in " ^ us wall ^ " of wall; measured " ^ us cpu)
  val _ = assert "the outer interval covers the inner burn" (cpu >= Time.fromMilliseconds 40)
  val _ = assert "CPU never exceeds wall" (cpu <= wall + tick)

  (*sleeping accrues no CPU*)
  val cpu = own_cpu OS.Process.sleep (Time.fromMilliseconds 50)
  val _ = writeln ("own clock: slept 50 ms wall, thread CPU " ^ us cpu)
  val _ = assert "CPU of a 50 ms sleep below 5 ms" (cpu < Time.fromMilliseconds 5)
\<close>

ML \<open>
  (*another thread reads this clock: while the worker is parked and the parent
    burns -- a blocked thread accrues no CPU whatever the load, so a clock that
    were really the parent's or the process's would move by the burn -- then
    while the worker burns and the parent only sleeps, and after the worker has
    ended.  The worker burns until told to stop, so the observation cannot
    outlive it*)
  val published = Synchronized.var "clock" (NONE: Thread_CPU.clock option)
  val go = Synchronized.var "thread_cpu_test_go" false
  val stop = Synchronized.var "thread_cpu_test_stop" false
  val worker =
    Isabelle_Thread.fork (Isabelle_Thread.params "thread_cpu_test") (fn () =>
      let
        val clock = Thread_CPU.the_self ()
        val backstop = Time.now () + Time.fromSeconds 30
        val x = Unsynchronized.ref 1
      in
        Synchronized.change published (K (SOME clock));
        Synchronized.timed_access go (fn _ => SOME backstop) (fn b => if b then SOME ((), b) else NONE);
        while not (Synchronized.value stop) andalso Time.now () < backstop
        do x := (! x * 3 + 1) mod 1000003
      end)
  val clock =
    Synchronized.guarded_access published (fn NONE => NONE | SOME c => SOME (c, SOME c))

  val p0 = reading clock
  val _ = burn_cpu (Time.fromMilliseconds 50)
  val p1 = reading clock
  val _ = writeln ("cross-thread: the parent burned 50 ms while the worker was parked; \
    \the worker's clock moved " ^ us (p1 - p0))
  val _ = assert "the parent read the worker's clock, not its own"
    (p1 - p0 < Time.fromMilliseconds 5 + tick)

  val _ = Synchronized.change go (K true)
  val c0 = reading clock
  val _ = poll_on "the parent never saw 50 ms of the worker's CPU" clock (Time.fromMilliseconds 50)
  val c1 = reading clock
  val _ = writeln ("cross-thread: the parent saw the worker's clock advance " ^ us (c1 - c0) ^
    " while only sleeping")
  val _ = Synchronized.change stop (K true)
  val _ = Isabelle_Thread.join worker
  val final = Thread_CPU.read clock
  val _ =
    if ML_System.platform_is_windows then
      (*thread_cpu.c: the duplicated handle keeps the final total until free*)
      (assert "Windows: the final total stays readable" (is_some final);
       assert "Windows: and it no longer changes" (final = Thread_CPU.read clock))
    else
      (*thread_cpu.c: NONE once the thread is gone, a few microseconds after the join*)
      let
        val backstop = Time.now () + Time.fromSeconds 1
        fun wait () =
          if is_none (Thread_CPU.read clock) then ()
          else if Time.now () > backstop then error "read after the thread ended is still SOME after 1 s"
          else wait ()
      in wait () end
  val _ = Thread_CPU.free clock
\<close>

section \<open>The timeout\<close>

ML \<open>
  val _ = assert "normal completion returns the value"
    (cpu_apply (Time.fromSeconds 1) (fn () => 42) () = 42)

  (*a limit is charged in the thread's CPU: report overshoot and wall - CPU*)
  fun fire_once limit =
    let
      val wall0 = Time.now ()
      val r = Exn.capture (cpu_apply limit spin) ()
      val wall = Time.now () - wall0
    in
      (case r of
        Exn.Exn (Timeout.TIMEOUT cpu) => (cpu, wall)
      | Exn.Exn exn => error ("expected Timeout.TIMEOUT, got " ^ Runtime.exn_message exn)
      | Exn.Res _ => error "spin returned")
    end

  val (cpu, wall) = fire_once (Time.fromMilliseconds 50)
  val _ = writeln ("apply 50 ms: TIMEOUT at CPU " ^ us cpu ^ ", wall " ^ us wall)
  val _ = assert "fired at or after the limit" (cpu >= Time.fromMilliseconds 50)
  val _ = assert "fired within slack of the limit" (cpu - Time.fromMilliseconds 50 <= slack)

  (*no stale interrupt is left behind*)
  val _ = expect_no_interrupt ()
  val _ = assert "still alive after the timeout" (cpu_apply (Time.fromSeconds 1) (fn () => 1) () = 1)
\<close>

ML \<open>
  (*overshoot statistics: 20 limits of 20 ms.  wall - CPU is the thread's
    deschedule time, unbounded on a busy machine: printed, never asserted*)
  val samples = map (fn _ => fire_once (Time.fromMilliseconds 20)) (1 upto 20)
  val overs = map (fn (cpu, _) => cpu - Time.fromMilliseconds 20) samples
  val descheduled = map (fn (cpu, wall) => wall - cpu) samples
  fun stats xs =
    let
      val n = length xs
      val total = fold (curry op +) xs Time.zeroTime
      val mean = Time.fromMicroseconds (Time.toMicroseconds total div n)
      val sorted = sort Time.compare xs
    in "min " ^ us (hd sorted) ^ ", mean " ^ us mean ^ ", max " ^ us (List.last sorted) end
  val _ = writeln ("20 x apply 20 ms: CPU overshoot  " ^ stats overs)
  val _ = writeln ("20 x apply 20 ms: wall - CPU     " ^ stats descheduled)
  val _ = assert "every sample fired at or after its limit"
    (forall (fn t => t >= Time.zeroTime) overs)
  val _ = assert "every sample fired within slack of its limit"
    (forall (fn t => t <= slack) overs)
\<close>

ML \<open>
  (*a foreign interrupt -- one this module did not cause, here a cancellation
    from another thread -- stays an interrupt.  It MUST come from another
    thread: Isabelle_Thread.interrupt_thread stores the break flag only after
    Thread.Thread.interrupt returns (isabelle_thread.ML:145-147), so a thread
    interrupting itself unwinds first, loses the flag, and the interrupt
    arrives as Interrupt_Breakdown -- the case the NEXT block tests on purpose.
    (A self-interrupt inside the body was tried and asserts false.)  The
    interrupter waits until the body is running, so the interrupt provably
    lands after the registration and not before apply is entered.*)
  val target = Isabelle_Thread.self ()
  val entered = Synchronized.var "thread_cpu_test_entered" false
  val _ =
    Isabelle_Thread.fork (Isabelle_Thread.params "thread_cpu_test_interrupter") (fn () =>
      (Synchronized.guarded_access entered (fn b => if b then SOME ((), b) else NONE);
       Isabelle_Thread.interrupt_thread target))
  val r =
    Exn.capture (cpu_apply (Time.fromSeconds 60)
      (fn () => (Synchronized.change entered (K true); spin ()))) ()
  val _ = assert "a foreign interrupt is re-raised, not dressed as TIMEOUT"
    (Exn.is_interrupt_proper_exn r andalso
     (case r of Exn.Exn (Timeout.TIMEOUT _) => false | _ => true))
  val _ = expect_no_interrupt ()
  val _ = assert "the withdrawn registration is gone" (cpu_apply (Time.fromSeconds 1) (fn () => 1) () = 1)
\<close>

ML \<open>
  (*the Breakdown claim (thread_cpu.ML `ours'): a Breakdown is ours only after we fired*)

  (*negative: nothing fired, a Breakdown from the body is released unchanged*)
  val r: unit Exn.result =
    Exn.capture (cpu_apply (Time.fromSeconds 10) (fn () => raise Exn.Interrupt_Breakdown)) ()
  val _ = assert "a Breakdown before firing stays a Breakdown"
    (case r of Exn.Exn exn => Exn.is_interrupt_breakdown exn | _ => false)

  (*after firing: consume the manager's real interrupt with interrupts deferred,
    then raise as instructed -- with nothing pending and no proper interrupt
    anywhere, only the Breakdown clause can turn this into TIMEOUT.  The
    flag-loss race on the flush limb itself cannot be provoked on purpose and
    is deliberately untested.*)
  fun after_firing raise_it =
    Thread_Attributes.with_attributes Thread_Attributes.no_interrupts (fn _ =>
      let
        val backstop = Time.now () + Time.fromSeconds 10
        val x = Unsynchronized.ref 1
        fun wait () =
          if Exn.is_interrupt_exn (Isabelle_Thread.expose_interrupt_result ()) then ()
          else if Time.now () > backstop then error "the manager never fired"
          else (x := (! x * 3 + 1) mod 1000003; wait ())
      in wait (); raise_it () end)

  (*positive: a bare Breakdown after firing is claimed*)
  val r: unit Exn.result =
    Exn.capture (cpu_apply (Time.fromMilliseconds 20) after_firing) (fn () => raise Exn.Interrupt_Breakdown)
  val _ = assert "a Breakdown after firing becomes TIMEOUT"
    (case r of Exn.Exn (Timeout.TIMEOUT _) => true | _ => false)
  val _ = expect_no_interrupt ()

  (*discriminator: a Par_Exn with a real failure beside the Breakdown is not all-Breakdown*)
  val r: unit Exn.result =
    Exn.capture (cpu_apply (Time.fromMilliseconds 20) after_firing)
      (fn () => raise Par_Exn.make [Exn.Interrupt_Breakdown, ERROR "real failure"])
  val _ = assert "a real failure beside a Breakdown is not claimed"
    (case r of Exn.Exn (Timeout.TIMEOUT _) => false | Exn.Exn exn => is_some (Par_Exn.dest exn) | _ => false)
  val _ = expect_no_interrupt ()
\<close>

ML \<open>
  (*a blocked thread accrues no CPU: the limit does not fire (the liveness contract)*)
  val wall0 = Time.now ()
  val _ = cpu_apply (Time.fromMilliseconds 20) OS.Process.sleep (Time.fromMilliseconds 100)
  val _ = writeln ("apply 20 ms over a 100 ms sleep: returned normally after " ^ ms (Time.now () - wall0))
\<close>

ML \<open>
  (*several guarded threads at once: every one fires on its own limit*)
  val n = 8
  val results =
    Par_List.map (fn i =>
      Exn.capture (cpu_apply (Time.fromMilliseconds (10 * i)) spin) ()) (1 upto n)
  val cpus =
    map (fn Exn.Exn (Timeout.TIMEOUT cpu) => cpu
          | Exn.Exn exn => error ("expected Timeout.TIMEOUT, got " ^ Runtime.exn_message exn)
          | Exn.Res _ => error "spin returned") results
  val _ = writeln ("8 concurrent limits 10..80 ms fired at: " ^ commas (map us cpus))
  val _ = assert "each concurrent limit fired within [limit, limit + slack]"
    (forall (fn (i, cpu) =>
        Time.fromMilliseconds (10 * i) <= cpu andalso
        cpu - Time.fromMilliseconds (10 * i) <= slack)
      (1 upto n ~~ cpus))
\<close>

ML \<open>
  (*nesting with the wall-clock timeout, both ways*)
  fun timeout_of r =
    (case r of Exn.Exn (Timeout.TIMEOUT t) => t | _ => error "expected TIMEOUT")

  val cpu_inside =
    timeout_of (Exn.capture (Timeout.apply (Time.fromSeconds 5) (cpu_apply (Time.fromMilliseconds 30) spin)) ())
  val _ = writeln ("CPU 30 ms inside wall 5 s: TIMEOUT at " ^ us cpu_inside)
  val _ = assert "the inner CPU limit fired"
    (Time.fromMilliseconds 30 <= cpu_inside andalso cpu_inside <= Time.fromMilliseconds 30 + slack)

  val wall_inside =
    timeout_of (Exn.capture (cpu_apply (Time.fromSeconds 5) (Timeout.apply (Time.fromMilliseconds 30) spin)) ())
  val _ = writeln ("wall 30 ms inside CPU 5 s: TIMEOUT at " ^ us wall_inside)
  val _ = assert "the inner wall limit fired, not the outer CPU limit" (wall_inside < Time.fromSeconds 1)
  val _ = expect_no_interrupt ()

  (*self-nesting: two registrations on one thread, either one due first*)
  val inner_first =
    timeout_of (Exn.capture (cpu_apply (Time.fromMilliseconds 200) (cpu_apply (Time.fromMilliseconds 30) spin)) ())
  val _ = writeln ("CPU 30 ms inside CPU 200 ms: TIMEOUT at " ^ us inner_first)
  val _ = assert "the inner registration fired and the outer let it through"
    (Time.fromMilliseconds 30 <= inner_first andalso inner_first <= Time.fromMilliseconds 30 + slack)
  val _ = expect_no_interrupt ()

  val outer_first =
    timeout_of (Exn.capture (cpu_apply (Time.fromMilliseconds 30) (cpu_apply (Time.fromMilliseconds 200) spin)) ())
  val _ = writeln ("CPU 200 ms inside CPU 30 ms: TIMEOUT at " ^ us outer_first)
  val _ = assert "the outer registration fired; the inner declined and re-raised"
    (Time.fromMilliseconds 30 <= outer_first andalso outer_first <= Time.fromMilliseconds 30 + slack)
  val _ = expect_no_interrupt ()
\<close>

section \<open>The measurement\<close>

ML \<open>
  val ({thread_cpu, elapsed, ...}, ()) = Thread_CPU.timing burn_cpu (Time.fromMilliseconds 40)
  val cpu = (case thread_cpu of SOME t => t | NONE => error "timing: no thread CPU")
  val _ = writeln ("timing: burned 40 ms of CPU; thread " ^ us cpu ^ ", elapsed " ^ us elapsed)
  val _ = assert "timing covers the burn" (cpu >= Time.fromMilliseconds 40)
  val _ = assert "timing: thread CPU never exceeds elapsed" (cpu <= elapsed + tick)

  val (thread_cpu, ()) = Thread_CPU.cpu_timing OS.Process.sleep (Time.fromMilliseconds 50)
  val cpu = (case thread_cpu of SOME t => t | NONE => error "cpu_timing: no thread CPU")
  val _ = writeln ("cpu_timing: slept 50 ms wall, thread CPU " ^ us cpu)
  val _ = assert "cpu_timing of a 50 ms sleep below 5 ms" (cpu < Time.fromMilliseconds 5)

  (*an exception passes through unmeasured*)
  val r = Exn.capture (Thread_CPU.timing (fn () => error "inside": unit)) ()
  val _ = assert "timing lets the body's exception through"
    (case r of Exn.Exn (ERROR "inside") => true | _ => false)
  val _ = assert "another measurement still works after the exception"
    (is_some (fst (Thread_CPU.cpu_timing (fn () => ()) ())))
\<close>

section \<open>The two limits\<close>

ML \<open>
  (*both given: whichever comes first fires, and the exception carries that
    limit's own clock -- CPU spent, or wall elapsed*)
  val cpu_first =
    timeout_of (Exn.capture (Thread_CPU.apply {thread_cpu = Time.fromMilliseconds 30, wall = SOME (Time.fromSeconds 5)} spin) ())
  val _ = writeln ("cpu 30 ms, wall 5 s: TIMEOUT at " ^ us cpu_first)
  val _ = assert "the CPU limit fired"
    (Time.fromMilliseconds 30 <= cpu_first andalso cpu_first <= Time.fromMilliseconds 30 + slack)
  val _ = expect_no_interrupt ()

  val wall0 = Time.now ()
  val wall_first =
    timeout_of (Exn.capture (Thread_CPU.apply {thread_cpu = Time.fromSeconds 5, wall = SOME (Time.fromMilliseconds 30)} spin) ())
  val elapsed = Time.now () - wall0
  val _ = writeln ("cpu 5 s, wall 30 ms: TIMEOUT at " ^ us wall_first ^ " after " ^ us elapsed)
  val _ = assert "the wall limit fired, long before the CPU limit"
    (Time.fromMilliseconds 30 <= wall_first andalso elapsed < Time.fromSeconds 1)
  val _ = expect_no_interrupt ()

  (*the wall limit is the liveness guard: a blocked thread reaches it.  Poly/ML
    wakes a sleeping thread at 1 s granularity, hence the 2 s bound; the
    payload is that limit's own clock, wall elapsed*)
  val wall0 = Time.now ()
  val r = Exn.capture (Thread_CPU.apply {thread_cpu = Time.fromMilliseconds 20, wall = SOME (Time.fromMilliseconds 100)} OS.Process.sleep) (Time.fromSeconds 5)
  val elapsed = Time.now () - wall0
  val _ = writeln ("cpu 20 ms, wall 100 ms over a 5 s sleep: TIMEOUT after " ^ ms elapsed)
  val _ = assert "the wall limit ended the sleep" (elapsed < Time.fromSeconds 2)
  val _ = assert "and its TIMEOUT carries wall elapsed"
    (case r of Exn.Exn (Timeout.TIMEOUT t) => Time.fromMilliseconds 100 <= t | _ => false)
  val _ = expect_no_interrupt ()

  (*an ignored CPU limit is no limit: a real burn does not fire it, and with a
    wall limit only that limit remains*)
  val _ = Thread_CPU.apply {thread_cpu = Time.zeroTime, wall = NONE} burn_cpu (Time.fromMilliseconds 50)
  val wall0 = Time.now ()
  val r = Exn.capture (Thread_CPU.apply {thread_cpu = Time.zeroTime, wall = SOME (Time.fromMilliseconds 30)} spin) ()
  val elapsed = Time.now () - wall0
  val _ = assert "thread_cpu = 0 with a wall limit: the wall limit fires, and not before its time"
    ((case r of Exn.Exn (Timeout.TIMEOUT _) => true | _ => false) andalso
     Time.fromMilliseconds 30 <= elapsed)
  val _ = expect_no_interrupt ()
\<close>

section \<open>timeout_scale\<close>

ML \<open>
  (*the default option is changed and restored; it round-trips as a string,
    so the restoration is exact.  It is process-wide, though: meanwhile every
    Timeout.apply in the process is scaled too -- one more reason this theory
    is run by hand, in a process of its own*)
  val (cpu, _) =
    Thread_Attributes.uninterruptible_body (fn run =>
      let
        val saved = Options.get_default "timeout_scale"
        val _ = Options.put_default "timeout_scale" "4.0"
        val result = Exn.capture0 (fn () => run fire_once (Time.fromMilliseconds 20)) ()
      in Options.put_default "timeout_scale" saved; Exn.release result end)
  val _ = writeln ("apply 20 ms under timeout_scale = 4: TIMEOUT at CPU " ^ us cpu)
  val _ = assert "a CPU limit is scaled by timeout_scale"
    (Time.fromMilliseconds 80 <= cpu andalso cpu <= Time.fromMilliseconds 80 + slack)
  val _ = expect_no_interrupt ()
\<close>

section \<open>Without the library\<close>

text \<open>
  Not exercised here, where the library is present, and not exercisable from a
  theory on a machine without it (the checks above need the clock).  The
  recipe, run by hand in about ten seconds:

    1. copy this component to a scratch directory;
    2. there, rename library/native/<platform> aside;
    3. over Pure, load a theory that asserts, in this order:
         is_none (Thread_CPU.self ());
         Thread_CPU.the_self () raises the loader's ERROR;
         Thread_CPU.timing reports thread_cpu = NONE beside the process figures;
         Thread_CPU.apply {thread_cpu = 20 ms, wall = SOME 100 ms} spin
           raises TIMEOUT at about 100 ms of wall, with the warning -- and a
           second identical call warns again;
         Thread_CPU.apply {thread_cpu = 1 s, wall = NONE} raises the error
           naming the loader's reason and the build command, and so does
           wall = SOME 500 us: a wall limit under 1 ms is no wall limit;
         Thread_CPU.apply {thread_cpu = 0, wall = NONE} (fn () => 7) () = 7,
           with neither warning nor error.
\<close>

ML \<open>writeln "Thread_CPU_Test: all checks passed"\<close>

end
