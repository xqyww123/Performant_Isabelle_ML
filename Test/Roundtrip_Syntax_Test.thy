(* Checks for library/roundtrip_syntax.ML.

   Run it by hand -- like every other test here, it is deliberately NOT in ROOT.
   Failure is an `error'; part 3 prints its measurements.

   Part 1 compares the elaborated text of hand-built terms literally and reads
   it back, one case per rule of the elaborated syntax.  Part 2 says what
   read_elaborated refuses.  Part 3 gives single terms to the printers, each
   with the level expected.  Part 4 is the two readers on hand-written text.
   Part 5 runs a sample of the facts of Main through the printer in three
   situations and counts the levels (about half a minute).

   Parts 1 and 3 read every text twice: as plain text, and in the form that
   Isar hands to an attribute or a command (Syntax.implode_input). *)
theory Roundtrip_Syntax_Test
  imports Main "../Performant_Isabelle_ML"
begin

definition hidden_one :: nat where "hidden_one = 1"
datatype hidden_t = HT
abbreviation (input) three :: nat where "three \<equiv> Suc (Suc (Suc 0))"

(*constants whose full names have no dot*)
setup \<open>fn thy => thy
  |> Sign.root_path
  |> Sign.add_consts
     [(Binding.name "dotless_c", \<^typ>\<open>nat\<close>, NoSyn),
      (Binding.name "dotless_p", \<^typ>\<open>'a\<close>, NoSyn)]
  |> Sign.restore_naming thy\<close>

hide_const hidden_one
hide_type hidden_t

ML \<open>
fun assert msg b = if b then () else error ("FAILED: " ^ msg);

fun same (t, u) = Envir.beta_eta_contract t aconv Envir.beta_eta_contract u;

(*plain text, and what Isar hands to an attribute*)
val forms = [I, Syntax.implode_input o Input.string];

fun failure f x =
  (case Exn.result f x of
    Exn.Exn exn => SOME exn
  | Exn.Res _ => NONE);

val ctxt0 = \<^context>;
val schematic = Proof_Context.set_mode Proof_Context.mode_schematic;
val body = Variable.set_body true ctxt0;
val (x_inner, ctxt_x) = Variable.add_fixes ["x"] body |>> the_single;
val (x_inner', ctxt_xx) = Variable.add_fixes ["x"] ctxt_x |>> the_single;

val natT = \<^typ>\<open>nat\<close>;
val boolT = \<^typ>\<open>bool\<close>;
val hiddenT = Type ("Roundtrip_Syntax_Test.hidden_t", []);
val hidden_one = Const ("Roundtrip_Syntax_Test.hidden_one", natT);
val dotless_c = Const ("dotless_c", natT);
fun order a = TFree (a, \<^sort>\<open>order\<close>);
fun eq (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u));
\<close>


text \<open>Part 1: the elaborated syntax, rule by rule\<close>

ML \<open>
local

(*the elaborated text of t is s, and s reads back to t*)
fun elaborated ctxt t s =
  let
    val s' = Roundtrip_Syntax.string_of_elaborated ctxt t;
    val _ = assert ("the text\n  expected: " ^ s ^ "\n  got:      " ^ s') (s = s');
  in
    forms |> List.app (fn form =>
      assert ("read_elaborated does not return the same term from: " ^ s)
        (same (t, Roundtrip_Syntax.read_elaborated ctxt (form s))))
  end;

val a = Free ("a", natT) and f = Free ("f", natT --> natT);

in

(*the mark of a proposition; constants that are not polymorphic carry no type*)
val _ = elaborated ctxt0 \<^prop>\<open>True \<and> False\<close>
  "PROP HOL.Trueprop (HOL.conj HOL.True HOL.False)";
val _ = elaborated ctxt0 \<^term>\<open>True \<and> False\<close> "HOL.conj HOL.True HOL.False";
val _ = elaborated ctxt0 (Free ("P", propT)) "PROP (P::prop)";

(*a polymorphic constant carries its type at every occurrence; a type variable
  its sort and a free variable its type at the first occurrence only*)
val _ =
  let val v = Free ("v", order "'a") in
    elaborated ctxt0
      (HOLogic.mk_Trueprop (HOLogic.mk_conj (HOLogic.mk_eq (v, v), HOLogic.mk_eq (v, v))))
      ("PROP HOL.Trueprop (HOL.conj " ^
        "((HOL.eq::('a::Orderings.order) \<Rightarrow> 'a \<Rightarrow> HOL.bool) (v::'a) v) " ^
        "((HOL.eq::'a \<Rightarrow> 'a \<Rightarrow> HOL.bool) v v))")
  end;

(*a constant without a dot*)
val _ = elaborated ctxt0 dotless_c "(CONST dotless_c)";
val _ = elaborated ctxt0 (Const ("dotless_p", natT)) "(CONST dotless_p::Nat.nat)";
val _ = elaborated ctxt0 (Free ("g", natT --> natT) $ dotless_c)
  "(g::Nat.nat \<Rightarrow> Nat.nat) (CONST dotless_c)";

(*an abbreviation is a constant like any other*)
val _ = elaborated (Proof_Context.set_mode Proof_Context.mode_abbrev ctxt0)
  (Const ("Roundtrip_Syntax_Test.three", natT)) "Roundtrip_Syntax_Test.three";

(*a hidden constant, a hidden type*)
val _ = elaborated ctxt0 hidden_one "Roundtrip_Syntax_Test.hidden_one";
val _ = elaborated ctxt0 (Free ("h", hiddenT)) "(h::Roundtrip_Syntax_Test.hidden_t)";

(*application: an argument that is not an atom is parenthesised*)
val _ = elaborated ctxt0 (f $ (f $ a))
  "(f::Nat.nat \<Rightarrow> Nat.nat) (f (a::Nat.nat))";
val _ = elaborated ctxt0 (Free ("g", natT --> natT --> natT) $ a $ a)
  "(g::Nat.nat \<Rightarrow> Nat.nat \<Rightarrow> Nat.nat) (a::Nat.nat) a";

(*abstraction: the type at the binder, the bound variable bare; redexes stay*)
val _ = elaborated ctxt0 (Abs ("z", natT, f $ Bound 0))
  "\<lambda>z::Nat.nat. (f::Nat.nat \<Rightarrow> Nat.nat) z";
val _ = elaborated ctxt0 (Abs ("z", natT, Bound 0) $ a)
  "(\<lambda>z::Nat.nat. z) (a::Nat.nat)";
val _ = elaborated ctxt0 (Free ("F", (natT --> natT) --> natT) $ Abs ("z", natT, Bound 0))
  "(F::(Nat.nat \<Rightarrow> Nat.nat) \<Rightarrow> Nat.nat) (\<lambda>z::Nat.nat. z)";

(*the name of a binder: distinct from every free variable of the whole term and
  from the enclosing binders; an internal name cleaned; never a keyword*)
val _ = elaborated ctxt0 (Abs ("y", natT, Free ("y", natT)))
  "\<lambda>ya::Nat.nat. (y::Nat.nat)";
val _ = elaborated ctxt0 (Free ("g", (natT --> natT) --> natT --> natT) $
    Abs ("y", natT, Bound 0) $ Free ("y", natT))
  "(g::(Nat.nat \<Rightarrow> Nat.nat) \<Rightarrow> Nat.nat \<Rightarrow> Nat.nat) (\<lambda>ya::Nat.nat. ya) (y::Nat.nat)";
val _ = elaborated ctxt0 (Abs ("x", natT, Abs ("x", boolT, Free ("g", natT --> boolT --> natT) $
    Bound 1 $ Bound 0)))
  "\<lambda>x::Nat.nat. \<lambda>xa::HOL.bool. (g::Nat.nat \<Rightarrow> HOL.bool \<Rightarrow> Nat.nat) x xa";
val _ = elaborated ctxt0 (Free ("g", (natT --> natT) --> (natT --> natT) --> natT) $
    Abs ("x", natT, Bound 0) $ Abs ("x", natT, Bound 0))
  ("(g::(Nat.nat \<Rightarrow> Nat.nat) \<Rightarrow> (Nat.nat \<Rightarrow> Nat.nat) \<Rightarrow> Nat.nat) " ^
    "(\<lambda>x::Nat.nat. x) (\<lambda>x::Nat.nat. x)");
val _ = elaborated ctxt0 (Abs ("uu_", natT, a)) "\<lambda>uu::Nat.nat. (a::Nat.nat)";
val _ = elaborated ctxt0 (Abs ("", natT, Bound 0)) "\<lambda>x::Nat.nat. x";
val _ = elaborated ctxt0 (Abs ("a.b", natT, Bound 0)) "\<lambda>x::Nat.nat. x";
val _ = elaborated ctxt0 (Abs ("id", natT, Bound 0)) "\<lambda>id::Nat.nat. id";
val _ = elaborated ctxt0 (Abs ("CONST", natT, Abs ("PROP", natT, f $ Bound 1)))
  "\<lambda>CONSTa::Nat.nat. \<lambda>PROPa::Nat.nat. (f::Nat.nat \<Rightarrow> Nat.nat) CONSTa";

(*a fixed variable is written by its external name*)
val _ = assert "the internal name of the fixed variable" (x_inner <> "x");
val _ = elaborated ctxt_x (f $ (f $ Free (x_inner, natT)))
  "(f::Nat.nat \<Rightarrow> Nat.nat) (f (x::Nat.nat))";
val _ = elaborated ctxt_xx
  (Free ("g", natT --> natT --> natT) $ Free (x_inner, natT) $ Free (x_inner', natT))
  ("(g::Nat.nat \<Rightarrow> Nat.nat \<Rightarrow> Nat.nat) (" ^ x_inner ^ "::Nat.nat) (x::Nat.nat)");

(*schematic variables, schematic type variables*)
val _ =
  let val T = TVar (("'a", 1), \<^sort>\<open>order\<close>) in
    elaborated (schematic ctxt0) (eq (Var (("x1", 2), T), Var (("y", 3), T)))
      ("PROP HOL.Trueprop ((HOL.eq::(?'a1::Orderings.order) \<Rightarrow> ?'a1 \<Rightarrow> HOL.bool) " ^
        "(?x1.2::?'a1) (?y3::?'a1))")
  end;
val _ = elaborated (schematic ctxt0)
  (Var (("P", 0), natT --> propT) $ Var (("n", 0), natT))
  "PROP (?P::Nat.nat \<Rightarrow> prop) (?n::Nat.nat)";

(*types and sorts*)
val _ = elaborated ctxt0 (Free ("p", \<^typ>\<open>(nat \<times> bool) list list\<close>))
  "(p::(Nat.nat, HOL.bool) Product_Type.prod List.list List.list)";
val _ = elaborated ctxt0 (Free ("p", \<^typ>\<open>((nat \<Rightarrow> bool) \<Rightarrow> nat, nat \<Rightarrow> bool) sum\<close>))
  "(p::((Nat.nat \<Rightarrow> HOL.bool) \<Rightarrow> Nat.nat, Nat.nat \<Rightarrow> HOL.bool) Sum_Type.sum)";
val _ = elaborated ctxt0 (Free ("p", \<^typ>\<open>(nat \<Rightarrow> bool) list \<Rightarrow> nat\<close>))
  "(p::(Nat.nat \<Rightarrow> HOL.bool) List.list \<Rightarrow> Nat.nat)";
val _ = elaborated ctxt0 (Logic.mk_type (TFree ("'a", \<^sort>\<open>type\<close>)))
  "(Pure.type::('a::HOL.type) itself)";
val _ = elaborated ctxt0 (Free ("p", TFree ("'a", [])) ) "(p::('a::{}))";
val _ = elaborated ctxt0 (Free ("p", TFree ("'a", \<^sort>\<open>{order,zero}\<close>)))
  "(p::('a::{Groups.zero, Orderings.order}))";
val _ = elaborated ctxt0
  (Free ("p", order "'a" --> TFree ("'b", \<^sort>\<open>type\<close>) --> order "'a"))
  "(p::('a::Orderings.order) \<Rightarrow> ('b::HOL.type) \<Rightarrow> 'a)";

(*one name at two types, one type variable at two sorts: an occurrence is bare
  exactly when its type or sort is the one written last*)
val _ = elaborated ctxt0
  (Free ("g", natT --> boolT --> boolT --> natT --> natT) $ Free ("x", natT) $
    Free ("x", boolT) $ Free ("x", boolT) $ Free ("x", natT))
  ("(g::Nat.nat \<Rightarrow> HOL.bool \<Rightarrow> HOL.bool \<Rightarrow> Nat.nat \<Rightarrow> Nat.nat) " ^
    "(x::Nat.nat) (x::HOL.bool) x (x::Nat.nat)");
val _ = elaborated ctxt0
  (Free ("g", order "'a" --> TFree ("'a", \<^sort>\<open>type\<close>) --> natT) $ Free ("p", order "'a"))
  "(g::('a::Orderings.order) \<Rightarrow> ('a::HOL.type) \<Rightarrow> Nat.nat) (p::('a::Orderings.order))";

(*meta-logical connectives*)
val _ =
  let val k = Free ("k", natT) in
    elaborated ctxt0 (Logic.all k (Logic.mk_implies (eq (k, k), eq (k, a))))
      ("PROP (Pure.all::(Nat.nat \<Rightarrow> prop) \<Rightarrow> prop) (\<lambda>k::Nat.nat. Pure.imp " ^
        "(HOL.Trueprop ((HOL.eq::Nat.nat \<Rightarrow> Nat.nat \<Rightarrow> HOL.bool) k k)) " ^
        "(HOL.Trueprop ((HOL.eq::Nat.nat \<Rightarrow> Nat.nat \<Rightarrow> HOL.bool) k (a::Nat.nat))))")
  end;

val _ = writeln "Part 1 passed";

end;
\<close>


text \<open>Part 2: what read_elaborated refuses, and how it finishes a term\<close>

ML \<open>
local

val read = Roundtrip_Syntax.read_elaborated;

val malformed_prefix = "Malformed elaborated term: ";

fun malformed ctxt s =
  assert ("not reported as malformed: " ^ s)
    (case failure (read ctxt) s of
      SOME (ERROR msg) => msg = malformed_prefix ^ quote s
    | _ => false);

(*an exception that is not the one of a malformed text*)
fun refused ctxt s =
  assert ("not refused: " ^ s)
    (case failure (read ctxt) s of
      SOME (ERROR msg) => not (String.isPrefix malformed_prefix msg)
    | SOME _ => true
    | NONE => false);

val bound = Variable.bind_term (("P", 0), \<^prop>\<open>True\<close>) (schematic ctxt0);

in

(*not in the grammar*)
val _ = malformed ctxt0 "";
val _ = malformed ctxt0 "HOL.True)";
val _ = malformed ctxt0 "(HOL.True";
val _ = malformed ctxt0 "HOL.True HOL.True PROP";
val _ = malformed ctxt0 "(x::Nat.nat) + x";
val _ = malformed ctxt0 "(x::Nat.nat) ''ab";
val _ = malformed ctxt0 "(CONST::Nat.nat)";
val _ = malformed ctxt0 "(PROP::Nat.nat)";
val _ = malformed ctxt0 "\<lambda>CONST::Nat.nat. CONST";
val _ = malformed ctxt0 "\<lambda>x. x";

(*a variable without a type, a type variable without a sort, a constant without
  a type that is polymorphic or not declared*)
val _ = malformed ctxt0 "x";
val _ = malformed ctxt0 "(x::'a)";
val _ = malformed ctxt0 "HOL.eq";
val _ = malformed ctxt0 "(CONST dotless_p)";
val _ = malformed ctxt0 "Roundtrip_Syntax_Test.no_such_constant";
val _ = malformed ctxt0 "(\<lambda>x::Nat.nat. x) x";

(*certification in the context*)
val _ = refused ctxt0 "(Roundtrip_Syntax_Test.no_such_constant::Nat.nat)";
val _ = refused ctxt0 "(HOL.True::Nat.nat)";
val _ = refused ctxt0 "(x::Nat.nat Nat.nat)";
val _ = refused ctxt0 "(x::('a::Roundtrip_Syntax_Test.no_such_class))";
val _ = refused ctxt0 "PROP HOL.True";
val _ = refused ctxt0 "(f::Nat.nat \<Rightarrow> Nat.nat) HOL.True";

(*the mode of the context*)
val _ = refused ctxt0 "(?x::Nat.nat)";
val _ = refused ctxt0 "(x::(?'a::HOL.type))";
val _ = assert "a schematic variable in mode_schematic"
  (read (schematic ctxt0) "(?x::(?'a::HOL.type))" = Var (("x", 0), TVar (("'a", 0), \<^sort>\<open>type\<close>)));

(*a term binding of the context, an abbreviation*)
val _ = assert "a bound schematic variable is replaced"
  (read bound "PROP (?P::prop)" = \<^prop>\<open>True\<close>);
val _ = assert "an abbreviation is expanded"
  (read ctxt0 "Roundtrip_Syntax_Test.three" = \<^term>\<open>Suc (Suc (Suc 0))\<close>);

(*hidden names are no obstacle; a hand-written text within the grammar is read*)
val _ = assert "a hidden constant"
  (read ctxt0 "Roundtrip_Syntax_Test.hidden_one" = hidden_one);
val _ = assert "parentheses and blanks"
  (read ctxt0 "( (HOL.conj)  ( HOL.True )\n ((HOL.False)) )" = \<^term>\<open>True \<and> False\<close>);

val _ = writeln "Part 2 passed";

end;
\<close>


text \<open>Part 3: single terms, each with the level expected\<close>

ML \<open>
local

fun string_of_level Roundtrip_Syntax.Plain = "Plain"
  | string_of_level Roundtrip_Syntax.Typed = "Typed"
  | string_of_level Roundtrip_Syntax.Sorted = "Sorted"
  | string_of_level Roundtrip_Syntax.Elaborated = "Elaborated";

(*the printer returns the level expected, and the reader of the contract returns
  the same term from its text*)
fun check (printer, reader) label ctxt t expected =
  let
    val result = printer ctxt t;
    val show = the_default "NONE" o Option.map string_of_level;
    val _ =
      assert (label ^ ": expected " ^ show expected ^ ", got " ^ show (Option.map #1 result) ^
          (case result of SOME (_, s) => "\n  " ^ s | NONE => ""))
        (Option.map #1 result = expected);
    val _ = result |> Option.app (fn (_, s) =>
      forms |> List.app (fn form =>
        assert (label ^ ": does not read back: " ^ s)
          (case reader ctxt (form s) of SOME u => same (t, u) | NONE => false)));
  in Option.map #2 result end;

val prop = check (Roundtrip_Syntax.string_of_prop, Roundtrip_Syntax.read_prop);
val term = check (Roundtrip_Syntax.string_of_term, Roundtrip_Syntax.read_term);

open Roundtrip_Syntax;

val nil_nat = Const (\<^const_name>\<open>Nil\<close>, \<^typ>\<open>nat list\<close>);
val schematic_eq =
  let val T = TVar (("'a", 1), \<^sort>\<open>order\<close>)
  in eq (Var (("x1", 2), T), Var (("y", 3), T)) end;
val numerals_and_order =
  let val v = Free ("v", order "'a") in
    HOLogic.mk_Trueprop (HOLogic.mk_conj (\<^term>\<open>42 = (42::int)\<close>,
      Const (\<^const_name>\<open>less_eq\<close>, order "'a" --> order "'a" --> boolT) $ v $ v))
  end;

in

(*hidden names*)
val _ = prop "a hidden constant" ctxt0 (eq (hidden_one, \<^term>\<open>1::nat\<close>)) (SOME Elaborated);
val _ = prop "a hidden type that only a variable shows" ctxt0
  (eq (Free ("h", hiddenT), Free ("h", hiddenT))) (SOME Elaborated);
val _ = prop "a hidden type that a constant shows" ctxt0
  (eq (Free ("h", hiddenT), Const ("Roundtrip_Syntax_Test.hidden_t.HT", hiddenT))) (SOME Plain);

(*what the system reader's type inference rejects*)
val _ =
  let val aT = TFree ("'a", \<^sort>\<open>type\<close>); val a = Free ("a", aT) in
    prop "a constant at a type variable whose sort lacks its class" ctxt0
      (eq (Const (\<^const_name>\<open>plus\<close>, aT --> aT --> aT) $ a $ a, a)) (SOME Elaborated)
  end;
val _ = prop "the sort type where the context declares another sort"
  (Variable.declare_typ (order "'a") ctxt0)
  (eq (Free ("a", TFree ("'a", \<^sort>\<open>type\<close>)), Free ("a", TFree ("'a", \<^sort>\<open>type\<close>))))
  (SOME Elaborated);

(*variables*)
val _ = prop "two fixed variables with one external name" ctxt_xx
  (eq (Free (x_inner, natT), Free (x_inner', natT))) (SOME Elaborated);
val _ = prop "a constant without a dot" ctxt0 (eq (dotless_c, dotless_c)) (SOME Plain);
val _ = prop "a constant without a dot where a variable of its name is fixed"
  (#2 (Variable.add_fixes ["dotless_c"] ctxt0)) (eq (dotless_c, dotless_c)) (SOME Elaborated);

(*the levels of the system printer, and the two skips*)
val _ = prop "schematic variables at a sort" (schematic ctxt0) schematic_eq (SOME Sorted);
val _ = prop "the same, show_types on" (Config.put show_types true (schematic ctxt0))
  schematic_eq (SOME Sorted);
val _ = prop "the same, show_sorts on" (Config.put show_sorts true (schematic ctxt0))
  schematic_eq (SOME Plain);
val _ = prop "numerals and a variable at a sort" ctxt0 numerals_and_order (SOME Sorted);
val _ = prop "numerals, show_sorts on" (Config.put show_sorts true ctxt0)
  (eq (\<^term>\<open>(42::int, ''ab'')\<close>, \<^term>\<open>(42::int, ''ab'')\<close>)) (SOME Typed);

(*the mark of a proposition: the system reader alone reads the elaborated text*)
val _ =
  let
    val t = eq (nil_nat, nil_nat);
    val s = the (prop "a polymorphic constant without any variable" ctxt0 t (SOME Elaborated));
  in assert "Syntax.read_prop on the elaborated text" (same (t, Syntax.read_prop ctxt0 s)) end;

(*term bindings and the mode*)
val _ =
  let
    val ctxt = Variable.bind_term (("P", 0), \<^prop>\<open>True\<close>) (schematic ctxt0);
    val unbound = Vartab.fold (Variable.unbind_term o #1) (Variable.binds_of ctxt) ctxt;
    val _ = prop "a schematic variable that the context binds" ctxt (Var (("P", 0), propT)) NONE;
    val _ = prop "the same without the bindings" unbound (Var (("P", 0), propT)) (SOME Plain);
  in () end;
val _ =
  let val T = HOLogic.mk_setT (TVar (("'a", 0), \<^sort>\<open>type\<close>)) in
    prop "a schematic type variable outside mode_schematic" ctxt0
      (HOLogic.mk_Trueprop (HOLogic.mk_not
        (HOLogic.mk_eq (HOLogic.mk_UNIV (TVar (("'a", 0), \<^sort>\<open>type\<close>)),
          Const (\<^const_name>\<open>bot\<close>, T))))) NONE
  end;

(*what gives up*)
val _ = prop "a free variable with a dot" ctxt0
  (eq (Free ("a.b", natT), Free ("a.b", natT))) NONE;
val _ = prop "a free variable named like a constant of a fitting type" ctxt0
  (eq (Free ("id", natT --> natT), Free ("id", natT --> natT))) NONE;
val _ = prop "a free variable with the external name of a fixed variable" ctxt_x
  (eq (Free ("x", natT), Free ("x", natT))) NONE;
val _ = prop "a free variable named CONST" ctxt0
  (eq (Free ("CONST", natT), Free ("CONST", natT))) NONE;
val _ = prop "a free variable named PROP" ctxt0
  (eq (Free ("PROP", natT), Free ("PROP", natT))) NONE;
val _ = prop "an abbreviation that is not expanded" ctxt0
  (eq (Const ("Roundtrip_Syntax_Test.three", natT), \<^term>\<open>0::nat\<close>)) NONE;

(*terms that are not propositions*)
val _ = term "a polymorphic constant on its own" ctxt0 nil_nat (SOME Elaborated);
val _ = term "a hidden constant on its own" ctxt0 hidden_one (SOME Elaborated);
val _ =
  let
    val (y, ctxt) = Variable.add_fixes ["y"] ctxt_x |>> the_single;
    val t = \<^Const>\<open>plus natT\<close> $ Free (x_inner, natT) $ Free (y, natT);
  in
    term "fixed variables whose types the context knows" (Variable.declare_term t ctxt) t
      (SOME Plain)
  end;
val _ = term "a proposition printed as a term" ctxt0 (eq (nil_nat, nil_nat)) (SOME Elaborated);

val _ = writeln "Part 3 passed";

end;
\<close>


text \<open>Part 4: the two readers on text that no printer wrote\<close>

ML \<open>
val _ = assert "read_term on unreadable text" (Roundtrip_Syntax.read_term ctxt0 "x +" = NONE);
val _ = assert "read_prop on unreadable text" (Roundtrip_Syntax.read_prop ctxt0 "x +" = NONE);
val _ = assert "read_prop on an elaborated term that is no proposition"
  (Roundtrip_Syntax.read_prop ctxt0 "Roundtrip_Syntax_Test.hidden_one" = NONE);
val _ = assert "read_term on that text"
  (Roundtrip_Syntax.read_term ctxt0 "Roundtrip_Syntax_Test.hidden_one" = SOME hidden_one);
(*here the elaborated reader raises TYPE, not ERROR*)
val _ = assert "read_term on a constant that is not declared"
  (Roundtrip_Syntax.read_term ctxt0 "(Roundtrip_Syntax_Test.no_such_constant::Nat.nat)" = NONE);
val _ = assert "read_term on hand-written text"
  (Roundtrip_Syntax.read_term ctxt0 "Suc 0 = (n::nat)" = SOME \<^term>\<open>Suc 0 = (n::nat)\<close>);
val _ = assert "read_prop on hand-written text"
  (Roundtrip_Syntax.read_prop ctxt0 "Suc 0 = (n::nat)" = SOME \<^prop>\<open>Suc 0 = (n::nat)\<close>);

(*an interrupt is no failure, also when a Par_Exn carries it*)
local
  val cancelled = Context.proof_map (Syntax_Phases.term_check 0 "cancelled"
    (fn _ => fn _ => raise Par_Exn.make [ERROR "e", Exn.Interrupt_Breakdown])) ctxt0;
  fun interrupted read =
    (case failure (read cancelled) "x" of
      SOME exn => Interrupt_Family.contains_interrupt exn
    | NONE => false);
in
  val _ = assert "read_term raises the interrupt again" (interrupted Roundtrip_Syntax.read_term);
  val _ = assert "read_prop raises the interrupt again" (interrupted Roundtrip_Syntax.read_prop);
end;

val _ = writeln "Part 4 passed";
\<close>


text \<open>Part 5: a sample of the facts of Main, in three situations\<close>

ML \<open>
local

val sample =
  Global_Theory.all_thms_of \<^theory>\<open>Main\<close> false
  |> map (Thm.prop_of o #2)
  |> filter (fn t => size_of_term t <= 150)
  |> map_index I
  |> map_filter (fn (i, t) => if i mod 8 = 0 then SOME t else NONE);

open Roundtrip_Syntax;

fun run label prepare =
  let
    val start = Timing.start ();
    fun one prop (plain, typed, sorted, elaborated) =
      let
        val (t, ctxt) = prepare prop;
        fun failed what = error ("FAILED: " ^ label ^ ": " ^ what ^ ":\n" ^
          Syntax.string_of_term ctxt0 prop);
        val _ =
          same (t, read_elaborated ctxt (string_of_elaborated ctxt t)) orelse
            failed "the elaborated text does not read back";
      in
        (case string_of_prop ctxt t of
          NONE => failed "no text"
        | SOME (level, s) =>
            (case read_prop ctxt s of
              SOME u => if same (t, u) then () else failed "another term is read back"
            | NONE => failed "the text is not read back";
            case level of
              Plain => (plain + 1, typed, sorted, elaborated)
            | Typed => (plain, typed + 1, sorted, elaborated)
            | Sorted => (plain, typed, sorted + 1, elaborated)
            | Elaborated => (plain, typed, sorted, elaborated + 1)))
      end;
    val (plain, typed, sorted, elaborated) = fold one sample (0, 0, 0, 0);
  in
    writeln (label ^ ": " ^ string_of_int (length sample) ^ " propositions; Plain " ^
      string_of_int plain ^ ", Typed " ^ string_of_int typed ^ ", Sorted " ^
      string_of_int sorted ^ ", Elaborated " ^ string_of_int elaborated ^ "; " ^
      Timing.message (Timing.result start))
  end;

(*not visible: the system reader warns of ambiguous input*)
val silent = Context_Position.set_visible false;

fun import prop = Variable.import_terms true [prop] (silent body) |>> the_single;

in

val _ = run "as stated, with schematic variables" (fn prop => (prop, silent (schematic ctxt0)));
val _ = run "variables fixed, their types unknown to the context" import;
val _ = run "variables fixed, their types known to the context"
  (fn prop => let val (t, ctxt) = import prop in (t, Variable.declare_term t ctxt) end);

val _ = writeln "Part 5 passed";

end;
\<close>

end
