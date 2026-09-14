theory Event_Log_Marker_Probe
  imports Performant_Isabelle_ML.Performant_Isabelle_ML
begin

text \<open>TEMPORARY probe (2026-09-14): compiles the edited library/event_log.ML as a
  shadowing structure and checks the marker format end to end -- three records
  with newlines, escaped "<" and a marker-looking text, one comment, then
  read_file must give exactly the three records back byte-for-byte.  Delete
  after the heap rebuild lets Test/Event_Log_Test.thy run on the real code.\<close>

ML_file "../library/event_log.ML"

ML \<open>
  val cat =
    Event_Log.category {name = "marker_probe", enabled = fn () => true,
      encode = fn (props, body) => (props, body)}
  val texts =
    ["plain text",
     "line1\n<not-a-tag\n <!-- record -->\nend\n",
     "bad\^E\^Fchars\ttab -- dashes"]
  val _ = List.app (fn t => Event_Log.append cat ([("k", t)], [Event_Log.elem_text "payload" t])) texts
  val _ = Event_Log.comment cat "hand marker -- with <!-- record --> inside"
  val dir = the (Event_Log.log_dir ())
  val category_dir = Path.append dir (Path.basic "marker_probe")
  val suffix = "-" ^ string_of_int (ML_Pid.get ()) ^ ".xml"
  (*a re-evaluation of this block makes a fresh category value and a fresh file:
    the newest one is this evaluation's*)
  val file =
    (case sort_strings (filter (String.isSuffix suffix) (File.read_dir category_dir)) of
       [] => error "no file"
     | names => Path.append category_dir (Path.basic (List.last names)))
  val raw = File.read file
  val _ = writeln raw
  val trees = Event_Log.read_file file
  val payloads =
    map (fn XML.Elem (("record", _), [XML.Elem (("payload", _), [XML.Text s])]) => s
          | _ => error "unexpected tree") trees
  val expected = map (String.translate (fn c => if Char.ord c < 32 andalso not (member (op =) [#"\t", #"\n", #"\r"] c) then "" else str c)) texts
  val _ = if payloads = expected then writeln "round trip: 3 records byte-for-byte"
          else error ("round trip failed: " ^ commas (map quote payloads))
  val n_markers = length (Substring.tokens (fn c => c = #"\n") (Substring.full raw))
  val _ = if String.isPrefix "<!-- record -->\n" raw then writeln "file starts with the marker" else error "no leading marker"
\<close>

end
