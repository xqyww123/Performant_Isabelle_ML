(*  Title:  library/roundtrip_syntax.ML
    Author: Qiyuan Xu (with AI assistance)

Printing a term as text that reads back to the same term.

string_of_term and string_of_prop try four levels, from the most readable to
the most explicit, and return the first text that the reader of this file has
read back to the same term:

  Plain       the system printer (Syntax.pretty_term);
  Typed       the same with show_types;
  Sorted      the same with show_types and show_sorts;
  Elaborated  the elaborated syntax: the standard lambda syntax in which every
              constant is written by its full name, types are written where a
              reader needs them, and no notation is used.

NONE: no text reads back.  read_term and read_prop try the system reader first
and the reader of the elaborated syntax second; NONE: neither reads the text.

THE CONTRACT.  "The same term" is equality up to the names of bound variables
after beta-eta normalisation; types, sorts, and the names and indexes of
schematic variables are equal.

  string_of_term ctxt t = SOME (_, s)  ==>  read_term ctxt s = SOME u
  string_of_prop ctxt t = SOME (_, s)  ==>  read_prop ctxt s = SOME u

with u the same term as t.  It holds because the text is accepted by running
that very reader on it.  Moreover the system reader, given an accepted text,
either fails or returns the same term, and an accepted elaborated text is read
back by read_elaborated alone, so hidden names do not matter to it.

OBLIGATIONS ON THE CALLER.

  * The context of printing and the context of reading are equal: the fixed
    variables, the declared types and sorts, the theory, the mode, and the
    term bindings.
  * A term with schematic variables of its own is printed and read in
    Proof_Context.mode_schematic, in a context without the term bindings.
    In the default mode and in mode_schematic every reader replaces a
    schematic variable that the context binds (?thesis, let ?x = ...) by the
    term bound to it, so a term with such a variable gets NONE; in the default
    mode it rejects every other schematic variable and every schematic type
    variable.
  * The term has no loose bound variable.
  * string_of_prop and read_prop are for a term of type prop.

The readers take inner syntax the way Syntax.read_term takes it: plain text, or
Syntax.implode_input of a source.  The printers return plain text.

WHAT GETS NONE.  No text reads back for these terms, and nothing is built for
them: a term with a free or schematic variable whose name has a dot or is not
an identifier; with a free variable named CONST or PROP; with a free variable
that is not fixed but has the external name of a fixed one; with a free
variable that the context
neither fixes nor declares and that is named like an accessible constant of a
fitting type; a term that certification changes, such as one with an
abbreviation that is not expanded.

THE ELABORATED SYNTAX, as string_of_elaborated writes it.

  * A term of type prop starts with the mark "PROP ", so that Syntax.read_prop
    does not wrap it into an object-logic judgment.
  * A constant is written by its full name, "CONST c" when that name has no
    dot.  A constant that is not polymorphic carries no type; any other
    carries its type at every occurrence: (c::T).
  * A free or schematic variable carries its type at its first occurrence in
    the text, (x::T), and is bare afterwards.  A fixed variable is written by
    its external name.
  * An abstraction is written %x::T. b (with the lambda symbol); the name is
    made distinct from every free variable of the whole term and from the
    enclosing binders.  A bound variable is written bare.
  * A type variable carries its sort at its first occurrence, ('a::S), always,
    and is bare afterwards.  Types are written T => U (with the arrow symbol)
    or postfix by the full name of the constructor.

read_elaborated reads exactly this; it is not a reader for hand-written terms.
CONST and PROP are its keywords, as they are Isabelle's.
It resolves no name through a name space and infers no type, and then finishes
the term the way the system reader does (certification in the context, then
Proof_Context.standard_term_check_finish): abbreviations, term bindings and
the mode of the context mean what they mean to the system reader.
*)

signature ROUNDTRIP_SYNTAX =
sig
  datatype level = Plain | Typed | Sorted | Elaborated
  val string_of_term: Proof.context -> term -> (level * string) option
  val string_of_prop: Proof.context -> term -> (level * string) option
  val read_term: Proof.context -> string -> term option
  val read_prop: Proof.context -> string -> term option
  (*Elaborated alone, without any check*)
  val string_of_elaborated: Proof.context -> term -> string
  val read_elaborated: Proof.context -> string -> term
end;

structure Roundtrip_Syntax: ROUNDTRIP_SYNTAX =
struct

(*** The elaborated syntax ***)

(*words that the tokenizer never returns as an identifier*)
val keywords = ["CONST", "PROP"];

(*the type that a constant written without a type stands for; the table of
  constants is the one certification uses, abbreviations included*)
fun monomorphic_type ctxt c =
  (case try (Consts.type_scheme (Proof_Context.consts_of ctxt)) c of
    SOME T => if Term.exists_subtype Term.is_TVar T then NONE else SOME T
  | NONE => NONE);

(*Printer and reader go through the text from left to right and keep the same
  two tables: the type last written for each variable, and the sort last
  written for each type variable.  The printer writes an occurrence bare
  exactly when the table holds its type or sort, which is what the reader
  then gives it.  A free name x is the key (x, ~1).*)
type written = typ Vartab.table * sort Vartab.table;

val nothing_written: written = (Vartab.empty, Vartab.empty);


(** printing **)

local

fun str s ((written, text): written * string list) = (written, s :: text);

fun string_of_sort [c] = c
  | string_of_sort S = enclose "{" "}" (commas S);

fun type_variable (a, xi) S (st as ((types, sorts), text)) =
  if Vartab.lookup sorts xi = SOME S then str a st
  else
    ((types, Vartab.update (xi, S) sorts), text)
    |> fold str ["(", a, "::", string_of_sort S, ")"];

fun typ (Type ("fun", [T, U])) st = st |> type_atom T |> str " \<Rightarrow> " |> typ U
  | typ T st = type_atom T st
and type_atom (TFree (a, S)) st = type_variable (a, (a, ~1)) S st
  | type_atom (TVar (xi, S)) st = type_variable (Term.string_of_vname xi, xi) S st
  | type_atom (T as Type ("fun", [_, _])) st = st |> str "(" |> typ T |> str ")"
  | type_atom (Type (c, [])) st = str c st
  | type_atom (Type (c, [T])) st = st |> type_atom T |> str " " |> str c
  | type_atom (Type (c, T :: Ts)) st =
      st |> str "(" |> typ T |> fold (fn U => str ", " #> typ U) Ts |> str ") " |> str c;

fun typed name T st = st |> str "(" |> str name |> str "::" |> typ T |> str ")";

fun variable (name, xi) T (st as ((types, sorts), text)) =
  if Vartab.lookup types xi = SOME T then str name st
  else typed name T ((Vartab.update (xi, T) types, sorts), text);

in

fun string_of_elaborated ctxt t =
  let
    val extern = Proof_Context.extern_fixed ctxt;

    fun constant (c, T) =
      let val name = if Long_Name.is_qualified c then c else "CONST " ^ c in
        if monomorphic_type ctxt c <> SOME T then typed name T
        else if Long_Name.is_qualified c then str name
        else str "(" #> str name #> str ")"
      end;

    fun binder x =
      let val x' = Name.clean x
      in if Symbol_Pos.is_identifier x' then x' else "x" end;

    (*env: the names a binder must avoid, the names of the enclosing binders*)
    fun term (names, bs) (Abs (x, T, b)) st =
          let val (x', names') = Name.variant (binder x) names in
            st |> str "\<lambda>" |> str x' |> str "::" |> typ T |> str ". "
            |> term (names', x' :: bs) b
          end
      | term env t st = application env t st
    and application env (t $ u) st = st |> application env t |> str " " |> atom env u
      | application env t st = atom env t st
    and atom _ (Const c) st = constant c st
      | atom _ (Free (x, T)) st = let val x' = extern x in variable (x', (x', ~1)) T st end
      | atom _ (Var (xi, T)) st = variable (Term.string_of_vname xi, xi) T st
      | atom (_, bs) (Bound i) st = str (nth bs i) st
      | atom env t st = st |> str "(" |> term env t |> str ")";

    val names =
      Name.make_context keywords
      |> Term.fold_aterms (fn Free (x, _) => Name.declare (extern x) | _ => I) t;
    val mark = if Term.fastype_of t = propT then ["PROP "] else [];
  in implode (rev (#2 (term (names, []) t (nothing_written, mark)))) end;

end;


(** reading **)

local

datatype ty =
    Type_Variable of indexname * sort option
  | Type_Constructor of string * ty list;

datatype tm =
    Constant of string * ty option
  | Variable of indexname * ty option
  | Abstraction of string * ty * tm
  | Application of tm * tm;


(* the grammar *)

(*
  top   = PROP term | term
  term  = app | %id :: type. term
  app   = atom ... atom
  atom  = id | var | longid | ( const ) | ( const :: type ) | ( variable :: type ) | ( term )
  const = longid | CONST id
  type  = tapp => type | tapp
  tapp  = tatom name ... name
  tatom = name | tvar | ( tvar :: sort ) | ( type ) | ( type, ..., type ) name
  sort  = name | { name, ..., name }
  name  = longid | id
*)

val lexicon =
  Scan.make_lexicon (map Symbol.explode
    (["(", ")", "::", ".", ",", "{", "}", "\<lambda>", "\<Rightarrow>"] @ keywords));

fun $$ s =
  Scan.one (fn tok => Lexicon.is_literal tok andalso Lexicon.str_of_token tok = s);

fun kind k =
  Scan.some (fn tok =>
    if Lexicon.kind_of_token tok = k then SOME (Lexicon.str_of_token tok) else NONE);

fun enum1 sep scan = scan ::: Scan.repeat ($$ sep |-- scan);

val indexname = Lexicon.read_indexname o unprefix "?";

val ident = kind Lexicon.Ident;
val long_ident = kind Lexicon.Long_Ident;
val name = long_ident || ident;
val const = long_ident || $$ "CONST" |-- ident;
val variable = ident >> rpair ~1 || kind Lexicon.Var >> indexname;
val type_variable = kind Lexicon.Type_Ident >> rpair ~1 || kind Lexicon.Type_Var >> indexname;

val sort = name >> single || $$ "{" |-- Scan.optional (enum1 "," name) [] --| $$ "}";

fun typ toks =
 (type_application -- Scan.option ($$ "\<Rightarrow>" |-- typ) >>
    (fn (T, NONE) => T | (T, SOME U) => Type_Constructor ("fun", [T, U]))) toks
and type_application toks =
 (type_atom -- Scan.repeat name >>
    (fn (T, cs) => fold (fn c => fn U => Type_Constructor (c, [U])) cs T)) toks
and type_atom toks =
 (name >> (fn c => Type_Constructor (c, [])) ||
  type_variable >> (fn xi => Type_Variable (xi, NONE)) ||
  $$ "(" |-- type_variable -- ($$ "::" |-- sort) --| $$ ")" >>
    (fn (xi, S) => Type_Variable (xi, SOME S)) ||
  $$ "(" |-- typ :|-- (fn T =>
    $$ ")" >> K T ||
    Scan.repeat1 ($$ "," |-- typ) --| $$ ")" -- name >>
      (fn (Ts, c) => Type_Constructor (c, T :: Ts)))) toks;

fun term toks =
 ($$ "\<lambda>" |-- ident -- ($$ "::" |-- typ) -- ($$ "." |-- term) >>
    (fn ((x, T), b) => Abstraction (x, T, b)) ||
  atom -- Scan.repeat atom >>
    (fn (t, us) => fold (fn u => fn f => Application (f, u)) us t)) toks
and atom toks =
 (variable >> (fn xi => Variable (xi, NONE)) ||
  long_ident >> (fn c => Constant (c, NONE)) ||
  $$ "(" |-- const -- Scan.option ($$ "::" |-- typ) --| $$ ")" >> Constant ||
  $$ "(" |-- variable -- ($$ "::" |-- typ) --| $$ ")" >>
    (fn (xi, T) => Variable (xi, SOME T)) ||
  $$ "(" |-- term --| $$ ")") toks;

val top = Scan.option ($$ "PROP") -- term;

in

fun read_elaborated ctxt s =
  let
    val syms = Input.source_explode (Syntax.read_input s);
    fun malformed () = error ("Malformed elaborated term: " ^ quote (Symbol_Pos.content syms));

    fun typ_of (Type_Variable (xi, written_sort)) sorts =
          let
            val S =
              (case (written_sort, Vartab.lookup sorts xi) of
                (SOME S, _) => S
              | (NONE, SOME S) => S
              | (NONE, NONE) => malformed ());
            val T = (case xi of (a, ~1) => TFree (a, S) | _ => TVar (xi, S));
          in (T, Vartab.update (xi, S) sorts) end
      | typ_of (Type_Constructor (c, Ts)) sorts =
          fold_map typ_of Ts sorts |>> (fn Ts' => Type (c, Ts'));

    (*bs: the names of the enclosing binders*)
    fun term_of _ (Constant (c, SOME T)) (types, sorts) =
          let val (T', sorts') = typ_of T sorts
          in (Const (c, T'), (types, sorts')) end
      | term_of _ (Constant (c, NONE)) written =
          (case monomorphic_type ctxt c of
            SOME T => (Const (c, T), written)
          | NONE => malformed ())
      | term_of bs (Variable (xi, written_type)) (written as (types, sorts)) =
          (case (written_type, find_index (fn x => (x, ~1) = xi) bs) of
            (NONE, ~1) =>
              (case Vartab.lookup types xi of
                SOME T => (variable_of (xi, T), written)
              | NONE => malformed ())
          | (NONE, i) => (Bound i, written)
          | (SOME T, _) =>
              let val (T', sorts') = typ_of T sorts
              in (variable_of (xi, T'), (Vartab.update (xi, T') types, sorts')) end)
      | term_of bs (Abstraction (x, T, b)) (types, sorts) =
          let
            val (T', sorts') = typ_of T sorts;
            val (b', written') = term_of (x :: bs) b (types, sorts');
          in (Abs (x, T', b'), written') end
      | term_of bs (Application (t, u)) written =
          let
            val (t', written') = term_of bs t written;
            val (u', written'') = term_of bs u written';
          in (t' $ u', written'') end
    and variable_of ((x, ~1), T) = Free (the_default x (Variable.lookup_fixed ctxt x), T)
      | variable_of (xi, T) = Var (xi, T);

    val (mark, tm) =
      (case
        (Lexicon.tokenize lexicon {raw = false} syms handle ERROR _ => malformed ())
        |> filter Lexicon.is_proper
        |> Scan.read Lexicon.stopper top
       of
        SOME result => result
      | NONE => malformed ());
    val cert = if is_some mark then Proof_Context.cert_prop else Proof_Context.cert_term;
  in
    #1 (term_of [] tm nothing_written)
    |> cert ctxt
    |> singleton (Proof_Context.standard_term_check_finish ctxt)
  end;

end;



(*** The readers ***)

(*NONE: an exception that is not an interrupt.  The system reader raises
  ERROR, a Par_Exn, or Exn.EXCEPTIONS.  Not `try': it takes a Par_Exn that
  carries Exn.Interrupt_Breakdown for a failure.*)
fun attempt f x =
  (case Exn.result f x of
    Exn.Res y => SOME y
  | Exn.Exn exn => if Interrupt_Family.contains_interrupt exn then Exn.reraise exn else NONE);

fun read_term ctxt s =
  (case attempt (Syntax.read_term ctxt) s of
    NONE => attempt (read_elaborated ctxt) s
  | some => some);

fun read_prop ctxt s =
  (case attempt (Syntax.read_prop ctxt) s of
    NONE => attempt (read_elaborated ctxt) s |> Option.mapPartial (fn t =>
      if Term.fastype_of t = propT then SOME t else NONE)
  | some => some);



(*** The printers ***)

datatype level = Plain | Typed | Sorted | Elaborated;

local

fun same_term (t, u) = Envir.beta_eta_contract t aconv Envir.beta_eta_contract u;

(*plain text in one line*)
fun system_string_of ctxt t =
  Syntax.pretty_term (Config.put Printer.show_markup false ctxt) t
  |> Pretty.string_of_ops (Pretty.pure_output_ops (SOME 1000000));

(*a level whose options the context has on already would repeat an earlier one*)
fun system_levels ctxt =
  [(Plain, I)] @
  (if Config.get ctxt Printer.show_types then []
   else [(Typed, Config.put Printer.show_types true)]) @
  (if Config.get ctxt Printer.show_sorts then []
   else [(Sorted, Config.put Printer.show_types true #> Config.put Printer.show_sorts true)]);

fun string_of read ctxt t =
  let
    val silent = Context_Position.set_visible false ctxt;
    fun reads_back reader s =
      (case reader silent s of
        SOME u => same_term (t, u)
      | NONE => false);
    fun accept level s = if reads_back read s then SOME (level, s) else NONE;
  in
    (case get_first (fn (level, options) => accept level (system_string_of (options ctxt) t))
        (system_levels ctxt) of
      NONE =>
        let val s = string_of_elaborated ctxt t
        in if reads_back (attempt o read_elaborated) s then accept Elaborated s else NONE end
    | some => some)
  end;

in

val string_of_term = string_of read_term;
val string_of_prop = string_of read_prop;

end;

end;
