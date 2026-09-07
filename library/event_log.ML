(*  Title:  library/event_log.ML
    Author: Qiyuan Xu (with AI assistance)

Persistent event log: one pen shared by the whole Isabelle/ML dependency chain
(Performant_Isabelle_ML -> Auto_Sledgehammer -> Isa-Mini -> phi-system).  Any
code appends a categorized, timestamped record to an XML file on disk; a write
never raises and never changes the result of a proof.  Design and all rulings:
ai-artifacts/EVENT_LOG_PLAN.md.

File format (PLAN 5): one record = one top-level <record> element, serialized
by XML.string_of (which never emits newlines by itself, so newlines come only
from Text content), then made line-splittable by one mechanical transform: one
extra space is inserted after every newline that is followed by optional
spaces and "<".  Since "<" is always escaped inside text and attribute values,
"no line but the first begins with <" becomes a theorem; and because the
transform stuffs EVERY such line, the reader restores content byte-for-byte
by deleting exactly one space after every newline followed by spaces and "<".

Configuration (PLAN 2.2): the single environment variable
ISABELLE_EVENT_LOG_DIR.  Unset -> $ISABELLE_HOME_USER/event_log (default ON);
set to the empty string -> logging off.  Re-read on every use, never memoized:
a memoized value would be saved into session heaps and override a child
process's own environment.

Write discipline (PLAN 6): no held streams -- one File.append per record,
serialized by one Synchronized.var per category, which also memoizes the
(pid, file) pair of PLAN 2.4: session heap images inherit ML values
(ml_heap.ML:35-36), so the file path must be recomputed when the pid of the
running process differs from the memoized one.
*)

signature EVENT_LOG = sig
  type 'a category
  val category : {name: string, enabled: unit -> bool,
                  encode: 'a -> Properties.T * XML.body} -> 'a category
  val append   : 'a category -> 'a -> unit
  val comment  : 'a category -> string -> unit
  val log_dir  : unit -> Path.T option   (*NONE = logging off*)
  (*read a log file back: one tree per record, comments and corrupt items
    dropped -- the ML twin of tools/event_log.py*)
  val read_file : Path.T -> XML.tree list
  (*encoder helpers: long content goes into sub-elements, scalars into
    Properties.T directly; fields that may contain newlines must NOT be
    attributes (XML.parse and expat disagree on attribute newlines)*)
  val elem_text   : string -> string -> XML.tree
  val elem_pretty : string -> Pretty.T -> XML.tree
  val elem_list   : string -> ('a -> XML.tree) -> 'a list -> XML.tree
end

structure Event_Log : EVENT_LOG = struct

(* configuration *)

fun log_dir () =
  (case OS.Process.getEnv "ISABELLE_EVENT_LOG_DIR" of
    NONE => SOME (Path.expand (Path.explode "$ISABELLE_HOME_USER/event_log"))
  | SOME "" => NONE
  | SOME dir => SOME (Path.expand (Path.explode dir)))


(* categories *)

datatype 'a category = Category of
  {name: string,
   enabled: unit -> bool,   (*process-level switch; context-level switches
                              belong to call sites (PLAN 2.3)*)
   encode: 'a -> Properties.T * XML.body,
   state: (int * Path.T) option Synchronized.var}   (*mutex + (pid, file) memo*)

fun category {name, enabled, encode} =
  Category {name = name, enabled = enabled, encode = encode,
    state = Synchronized.var ("Event_Log." ^ name) NONE}


(* record boundary and character discipline (PLAN 5) *)

val filter_control =
  String.translate (fn c =>
    if Char.ord c >= 32 orelse c = #"\t" orelse c = #"\n" orelse c = #"\r"
    then str c else "")

(*must run AFTER filter_control: deleting a control byte could create "\n<"*)
fun stuff_boundaries s =
  (case String.fields (fn c => c = #"\n") s of
    [] => s
  | line0 :: lines =>
      let
        fun starts_tag line =
          Substring.isPrefix "<" (Substring.dropl (fn c => c = #" ") (Substring.full line))
      in
        String.concatWith "\n"
          (line0 :: map (fn l => if starts_tag l then " " ^ l else l) lines)
      end)


(* record attributes filled by append (PLAN 4) *)

fun timestamp_of time =
  let val ms = Time.toMilliseconds time mod 1000 in
    Date.fmt "%Y-%m-%dT%H:%M:%S" (Date.fromTimeLocal time) ^ "." ^
    StringCvt.padLeft #"0" 3 (string_of_int ms)
  end

fun standard_props name =
  let
    val theory_props =
      (case Option.mapPartial (try Context.theory_of) (Context.get_generic_context ()) of
        SOME thy => [("theory", Context.theory_long_name thy)]
      | NONE => [])
    val task_props =
      (case Future.worker_task () of
        SOME task =>
          [("task", Task_Queue.str_of_task task ^ " " ^ Task_Queue.str_of_task_groups task)]
      | NONE => [])
  in
    [("category", name), ("ts", timestamp_of (Time.now ()))] @
    theory_props @
    Position.properties_of (Position.thread_data ()) @
    [("thread", Isabelle_Thread.print (Isabelle_Thread.self ()))] @
    task_props
  end


(* writing (PLAN 6) *)

(*pure-ML recursive mkdir: Isabelle_System.make_directory goes through the
  Scala bridge, which a raw ML process does not have -- a logger must not
  depend on it.  An existence race with another process is harmless (the
  loser's SysErr is swallowed; a real failure surfaces at File.append).*)
fun make_directory path =
  if File.is_dir path then ()
  else
    (make_directory (Path.dir path);
     OS.FileSys.mkDir (File.platform_path path) handle OS.SysErr _ => ())

fun new_file dir name pid =
  let
    val category_dir = Path.append dir (Path.basic name)
    val _ = make_directory category_dir
    val file_name =
      Date.fmt "%Y-%m-%dT%H%M%S" (Date.fromTimeLocal (Time.now ())) ^
      "-" ^ string_of_int pid ^ ".xml"
  in Path.append category_dir (Path.basic file_name) end

val warned = Synchronized.var "Event_Log.warned" false

fun warn_once exn =
  Synchronized.change warned (fn already =>
    (if already then ()
     else Output.warning ("Event_Log: record dropped: " ^ General.exnMessage exn);
     true))

(*never raises (except reraising interrupts); non-interrupt failures are
  dropped, warning once per process -- NOT via the global Exn.capture_body,
  whose capture-and-discard would consume the thread's break flag (PLAN 3)*)
fun append_string (Category {name, enabled, state, ...}) make_string =
  (case log_dir () of
    NONE => ()
  | SOME dir =>
      if not (enabled ()) then ()
      else
        Thread_Attributes.uninterruptible_body (fn _ =>
          (case Exn.capture0 (fn () =>
              let val s = stuff_boundaries (filter_control (make_string ())) ^ "\n" in
                Synchronized.change state (fn memo =>
                  let
                    val pid = ML_Pid.get ()
                    val path =
                      (case memo of
                        SOME (pid', path') =>
                          if pid' = pid then path' else new_file dir name pid
                      | NONE => new_file dir name pid)
                    val _ = File.append path s
                  in SOME (pid, path) end)
              end) () of
            Exn.Res () => ()
          | Exn.Exn exn =>
              if Exn.is_interrupt exn then Exn.reraise exn else warn_once exn)))

fun append (cat as Category {name, encode, ...}) x =
  append_string cat (fn () =>
    let val (props, body) = encode x
    in XML.string_of (XML.Elem (("record", standard_props name @ props), body)) end)

(*human-written fixed markers only; "--" is illegal inside XML comments and is
  broken up, so the invariant cannot be violated*)
fun comment cat text =
  append_string cat (fn () =>
    let
      val text' =
        String.concat (rev (fold (fn c => fn acc =>
          if c = #"-" andalso (case acc of "-" :: _ => true | _ => false)
          then "-" :: " " :: acc else str c :: acc) (String.explode text) []))
    in "<!-- " ^ text' ^ " -->" end)


(* reading back *)

fun read_file path =
  let
    fun starts_tag line =
      Substring.isPrefix "<" (Substring.dropl (fn c => c = #" ") (Substring.full line))
    fun unstuff line =
      if String.isPrefix " " line andalso starts_tag line
      then String.extract (line, 1, NONE) else line
    (*group lines into items: an item begins at a line whose FIRST byte is "<"
      (the boundary theorem of the writer); continuation lines are unstuffed*)
    fun group ([], cur, items) = rev (rev cur :: items)
      | group (line :: rest, cur, items) =
          if String.isPrefix "<" line
          then group (rest, [line], if null cur then items else rev cur :: items)
          else group (rest, unstuff line :: cur, items)
    fun trim_blank lines = rev (drop_prefix (fn l => l = "") (rev lines))
    val items =
      (case split_lines (File.read path) of
        [] => []
      | lines => group (drop_prefix (fn l => not (String.isPrefix "<" l)) lines, [], []))
  in
    items
    |> map (String.concatWith "\n" o trim_blank)
    |> map_filter (fn "" => NONE | item => try XML.parse item)
  end


(* encoder helpers *)

fun elem_text name s = XML.Elem ((name, []), [XML.Text s])

fun elem_pretty name prt =
  elem_text name (Protocol_Message.clean_output (Pretty.string_of prt))

fun elem_list name f xs = XML.Elem ((name, []), map f xs)

end
