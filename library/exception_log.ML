(*  Title:  library/exception_log.ML
    Author: Qiyuan Xu (with AI assistance)

The exception category of Event_Log: structured exception records with frame
lists.  Design and all rulings: EVENT_LOG_PLAN.md (PLAN below).

The only working frame-trace mechanism is Exn_Debugger.capture_exception_trace
(Poly/ML's traceException is a no-op); its trace_var is a single-slot
thread-local, so frame capture can be active at most once per thread: the
OUTERMOST capture records, inner ones pass through (PLAN 3).  This also means
ML_exception_debugger gets an empty trace on a thread where capture is active
-- the documented cost of coexistence (PLAN 9).  Frames exist only for code
compiled under ML_debugger; elsewhere the hooks do not exist and the cost is
strictly zero.

The interrupt family never reaches the trace: Exn.result reraises interrupts
before stop_trace, so they fly out of capture_exception_trace directly.  We
catch them with the global Exn.capture_body -- which normalises a raw
interrupt via check_interrupt, consuming the thread's break flag exactly once,
the same as Isabelle_Thread.try_catch's interrupt branch -- and ALWAYS
reraise.  (Isabelle_Thread.check_interrupt itself is not exported;
capture-then-always-reraise is the reachable equivalent.  What PLAN 3 forbids
is capture-and-DISCARD.)  Interrupt_Breakdown is recorded traceless,
regardless of the record predicate: its diagnostic value is the first site
that sees it.
*)

signature EXCEPTION_LOG = sig
  type report = {site: string, exn: exn, trace: (string * Position.T) list}
  val category : report Event_Log.category
  val default_record : exn -> bool   (*excludes proper interrupts and Timeout.TIMEOUT*)
  val capture : {site: string, record: exn -> bool} -> (unit -> 'a) -> 'a
  (*record point helper for breakdown attribution: no-op unless the exception
    is -- or, inside a Par_Exn container, contains -- an Interrupt_Breakdown;
    never raises, never decides anything.  Ordinary record points still write
    Event_Log.append category {site, exn, trace = []} directly.*)
  val record_breakdown : string -> exn -> unit
end

structure Exception_Log : EXCEPTION_LOG = struct

type report = {site: string, exn: exn, trace: (string * Position.T) list}


(* encoding (PLAN 5) *)

val message_limit = 16384   (*bytes*)

fun message_elem exn =
  let val msg = Protocol_Message.clean_output (Runtime.exn_message exn) in
    if size msg <= message_limit
    then Event_Log.elem_text "message" msg
    else
      XML.Elem (("message", [("truncated_from", string_of_int (size msg))]),
        [XML.Text (String.substring (msg, 0, message_limit))])
  end

(*position of the raise, all standard position keys prefixed with "raised_"
  to avoid clashing with the record point's own position attributes (PIDE
  positions are offset-based and may carry no line; batch ones no offset)*)
fun raised_props exn =
  map (apfst (prefix "raised_"))
    (Position.properties_of (Exn_Properties.position exn))

fun stat_props () =
  let val stats = ML_Statistics.get () in
    ["size_stacks", "size_heap", "time_GC"]
    |> map_filter (fn key => Option.map (pair key) (AList.lookup (op =) stats key))
  end

(*frame list: compress adjacent identical frames, then truncate (PLAN 5);
  positions are the frame function's DEFINITION site, which is why merging
  adjacent identical entries is safe and the repeat count is the diagnosis*)
val max_written = 300
val keep_inner = 200
val keep_outer = 100

fun frame_key (fn_name, pos) =
  (fn_name, the_default "" (Position.file_of pos), the_default 0 (Position.line_of pos))

fun compress frames =
  rev (fold (fn frame => fn acc =>
    (case acc of
      (frame', n) :: rest =>
        if frame = frame' then (frame', n + 1) :: rest else (frame, 1) :: acc
    | [] => [(frame, 1)])) frames [])

fun frame_elem ((fn_name, file, line), n) =
  XML.Elem (("frame",
    ("fn", fn_name) ::
    (if file = "" then [] else [("file", file)]) @
    (if line = 0 then [] else [("line", string_of_int line)]) @
    (if n = 1 then [] else [("repeat", string_of_int n)])), [])

fun trace_elem [] = []
  | trace_elem frames =
      let
        val total = length frames
        val compressed = compress (map frame_key frames)
        val n_compressed = length compressed
        val (body, n_written) =
          if n_compressed <= max_written then (map frame_elem compressed, n_compressed)
          else
            let
              val inner = List.take (compressed, keep_inner)
              val outer = List.drop (compressed, n_compressed - keep_outer)
              val elided = List.take (List.drop (compressed, keep_inner),
                                      n_compressed - keep_inner - keep_outer)
              val elided_frames = fold (fn (_, n) => fn m => m + n) elided 0
            in
              (map frame_elem inner @
                XML.Elem (("elided", [("frames", string_of_int elided_frames)]), []) ::
               map frame_elem outer,
               keep_inner + keep_outer)
            end
      in
        [XML.Elem (("trace",
          [("total", string_of_int total),
           ("compressed", string_of_int n_compressed),
           ("written", string_of_int n_written)]), body)]
      end

fun encode {site, exn, trace} =
  let
    val props =
      ("site", site) :: ("exn", General.exnName exn) :: raised_props exn @ stat_props ()
    val exn_body =
      (case Par_Exn.dest exn of
        SOME exns =>   (*split the container: one <exn> per contained exception*)
          map (fn e =>
            XML.Elem (("exn", ("name", General.exnName e) :: raised_props e),
              [message_elem e])) exns
      | NONE => [message_elem exn])
  in (props, exn_body @ trace_elem trace) end

val category =
  Event_Log.category {name = "exception", enabled = fn () => true, encode = encode}


(* the record predicate (PLAN 4) *)

(*control-flow exception names (Success, Automation_Fail, ...) live upstairs;
  call sites stack their own exclusions on top of this one*)
fun default_record exn =
  not (Exn.is_interrupt_proper exn) andalso
  (case exn of Timeout.TIMEOUT _ => false | _ => true)


(* breakdown record points *)

(*a breakdown may sit inside a Par_Exn container (Par_Exn.make filters proper
  interrupts only) while is_interrupt of the container itself is false*)
fun record_breakdown site exn =
  if Exn.is_interrupt_breakdown exn orelse
      (case Par_Exn.dest exn of
        SOME exns => exists Exn.is_interrupt_breakdown exns
      | NONE => false)
  then Event_Log.append category {site = site, exn = exn, trace = []}
  else ()


(* frame capture (PLAN 4) *)

(*set only while FRAME capture is active on this thread -- record points and
  traceless appends do not touch it*)
val tracing_here = Thread_Data.var () : unit Thread_Data.var

fun convert_trace trace =
  map (apsnd Exn_Properties.position_of_polyml_location) trace

fun should_record record exn =
  (case Exn.capture0 record exn of Exn.Res b => b | Exn.Exn _ => true)

fun capture {site, record} body =
  if is_some (Thread_Data.get tracing_here) orelse is_none (Event_Log.log_dir ())
  then body ()   (*inner pass-through / logging off: plain call, zero cost*)
  else
    Thread_Attributes.uninterruptible_body (fn run =>
      (case Exn.capture_body (fn () =>
          Thread_Data.setmp tracing_here (SOME ())
            (fn () => Exn_Debugger.capture_exception_trace (run body)) ()) of
        Exn.Res (_, Exn.Res x) => x
      | Exn.Res (trace, Exn.Exn exn) =>
          ((if should_record record exn
            then Event_Log.append category
                   {site = site, exn = exn, trace = convert_trace trace}
            else ());
           Exn.reraise exn)
      | Exn.Exn exn =>   (*interrupt family, normalised; see header*)
          ((if Exn.is_interrupt_breakdown exn
            then Event_Log.append category {site = site, exn = exn, trace = []}
            else ());
           Exn.reraise exn)))

end
