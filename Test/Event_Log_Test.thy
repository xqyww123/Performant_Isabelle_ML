theory Event_Log_Test
  imports "../Performant_Isabelle_ML"
begin

text \<open>
  Unit test for Event_Log / Exception_Log (EVENT_LOG_PLAN.md, section 10.2).

  The theory writes records that stress the record-boundary transform, the
  control-character filter, the comment sanitizer, and the frame capture; it
  then injects one deliberately corrupt record and appends one more good one.
  The byte-for-byte round-trip and the skip-one-bad-record property are
  verified externally by tools/event_log.py -- run this theory with
  ISABELLE_EVENT_LOG_DIR pointing to a scratch directory (the theory refuses
  to run otherwise, because of the corrupt-record injection).
\<close>

ML \<open>
  val _ =
    (case OS.Process.getEnv "ISABELLE_EVENT_LOG_DIR" of
      SOME "" => error "Event_Log_Test: logging is off (ISABELLE_EVENT_LOG_DIR is empty)"
    | SOME dir => writeln ("Event_Log_Test: logging to " ^ dir)
    | NONE =>
        error "Event_Log_Test must run with ISABELLE_EVENT_LOG_DIR set to a scratch directory")
\<close>

section \<open>Plain records, boundary transform, control characters, comment\<close>

ML \<open>
  val test_category =
    Event_Log.category {name = "event_log_test", enabled = fn () => true,
      encode = fn (props, body) => (props, body)}

  (*1: plain*)
  val _ = Event_Log.append test_category
    ([("k", "v1")], [Event_Log.elem_text "payload" "plain text"])

  (*2: boundary stress -- a text node ending in a newline right before an
    element (the stuffing point), and content that already looks stuffed
    (newline + space + escaped "<"), which the bijective transform must
    return byte-for-byte*)
  val boundary_text = "line1\nline2\n"
  val tricky_text = " <not-a-tag\nend\n"
  val _ = Event_Log.append test_category
    ([("k", "v2")], [XML.Text boundary_text, Event_Log.elem_text "next" tricky_text])

  (*3: control characters (YXML bytes 5/6) are filtered, tab survives*)
  val _ = Event_Log.append test_category
    ([("k", "v3")], [Event_Log.elem_text "payload" "bad\^E\^Fchars\ttab"])

  val _ = Event_Log.comment test_category "hand marker -- double dash"
\<close>

section \<open>Frame capture\<close>

declare [[ML_debugger]]

ML \<open>
  (*non-tail recursion, so the unwind passes one debug frame per level*)
  fun deep 0 = raise Fail "boom"
    | deep n = deep (n - 1) + 0
  fun middle () = deep 400
\<close>

declare [[ML_debugger = false]]

ML \<open>
  local
    fun assert msg b = if b then () else error ("FAILED: " ^ msg)
    val record = Exception_Log.default_record
  in
    val _ = assert "success path returns the value"
      (Exception_Log.capture {site = "Event_Log_Test.ok", record = record}
        (fn () => 6 * 7) = 42)

    val _ =
      (case Exn.capture0
              (fn () =>
                Exception_Log.capture {site = "Event_Log_Test.fail", record = record}
                  middle) () of
        Exn.Exn (Fail msg) => assert "reraised the original Fail" (msg = "boom")
      | _ => error "FAILED: expected Fail to escape the capture")

    (*nesting: the inner capture passes through, only the outer records*)
    val _ =
      (case Exn.capture0
              (fn () =>
                Exception_Log.capture {site = "Event_Log_Test.outer", record = record}
                  (fn () =>
                    Exception_Log.capture {site = "Event_Log_Test.inner", record = record}
                      middle)) () of
        Exn.Exn (Fail _) => ()
      | _ => error "FAILED: expected Fail to escape the nested captures")

    (*an exception excluded by the record predicate writes nothing*)
    val _ =
      (case Exn.capture0
              (fn () =>
                Exception_Log.capture {site = "Event_Log_Test.excluded", record = fn _ => false}
                  (fn () => raise Fail "quiet")) () of
        Exn.Exn (Fail _) => ()
      | _ => error "FAILED: expected Fail to escape the excluded capture")
  end
\<close>

section \<open>Corrupt-record injection and one more good record\<close>

ML \<open>
  val category_dir =
    Path.append (the (Event_Log.log_dir ())) (Path.basic "event_log_test")
  val pid_suffix = "-" ^ string_of_int (ML_Pid.get ()) ^ ".xml"
  val log_file =
    (case List.filter (String.isSuffix pid_suffix) (File.read_dir category_dir) of
      [name] => Path.append category_dir (Path.basic name)
    | names => error ("FAILED: expected exactly one log file, got: " ^ commas names))
  val _ = File.append log_file "<record category=\"event_log_test\" broken=\"yes\">no close\n"
  val _ = Event_Log.append test_category ([("k", "v4")], [])
  val _ = writeln ("EVENT_LOG_TEST_FILE=" ^ Path.implode log_file)
\<close>

end
