theory ScratchLooseExn
  imports Skel_Fuzz
begin

ML \<open>
(*what are the 354 raises in fuzz_loose?  print the first few exception messages*)
val shown = Unsynchronized.ref 0;
val _ =
  List.app (fn i =>
    if ! shown >= 6 then ()
    else
      let
        val _ = srand (31337 + i);
        val rules = map gen_rule2 (1 upto (3 + rand 6));
        val net = Merely_Rewrite.make_rules rules;
        val input = loosen true (gen_term (4 + rand 3) []);
        val r = Exn.capture (fn () =>
          Merely_Rewrite.rewrite_term_mode Merely_Rewrite.Skeleton opts net ctxt0 bvs6 input) ();
      in
        (case r of
          Exn.Exn (Merely_Rewrite.DIVERGES _) => ()
        | Exn.Exn e =>
            (shown := ! shown + 1;
             writeln ("seed " ^ string_of_int (31337 + i) ^
               "\n  input " ^ dump input ^
               "\n  EXN   " ^ Runtime.exn_message e))
        | _ => ())
      end)
    (1 upto 3000);
val _ = writeln ("shown " ^ string_of_int (! shown));
\<close>

end
