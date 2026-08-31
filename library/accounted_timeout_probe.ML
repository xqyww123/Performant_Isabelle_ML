(*TEMPORARY (INTERRUPT_BREAKDOWN_PLAN.md 6.2, R3, author ruling 2026-08-31):
  one Event_Log record per claim of the accounted timeout during the
  verification period -- a count with context, NOT an Exception_Log entry.
  Delete this file, its ML_file line, and Accounted_Timeout.claim_probe
  together once the verification is complete (PLAN 6.5).*)

val _ =
  let
    fun shape exn =
      if Exn.is_interrupt_breakdown exn then "Breakdown"
      else
        (case Par_Exn.dest exn of
          SOME exns => "Par_Exn[" ^ string_of_int (length exns) ^ "]"
        | NONE => General.exnName exn)
    fun task () =
      (case Future.worker_task () of
        SOME t => Task_Queue.name_of_task t
      | NONE => "-")
    val category =
      Event_Log.category {name = "accounted_timeout_claim", enabled = fn () => true,
        encode = fn {physical, timeout, elapsed, exn} =>
          ([("physical", Bool.toString physical),
            ("timeout_ms", string_of_int (Time.toMilliseconds timeout)),
            ("elapsed_ms", string_of_int (Time.toMilliseconds elapsed)),
            ("exn", shape exn),
            ("task", task ())], [])}   (*thread: recorded by Event_Log itself*)
  in Accounted_Timeout.claim_probe := Event_Log.append category end
