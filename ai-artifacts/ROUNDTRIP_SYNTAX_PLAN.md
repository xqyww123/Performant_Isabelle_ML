# Printing a term as text that reads back: four levels, and a reader (plan, 2026-11-25)

Status (2026-11-26 04:40 UTC): revision 6: revision 5 with the owner's ruling of 2026-11-26 04:37:26
written in: `CONST` and `PROP` are keywords of the elaborated reader (9.3).
Revisions 1 to 4 were reviewed (section 12); the owner ruled on their open points (section 9).
Each design point carries a label: [owner] is the owner's statement, [design] is my proposal.
No question is open for the owner.
The owner's word of 2026-11-26 04:37:26: the code may be written.
State of 2026-11-26 11:36 UTC: the library, its test and the entries in the documentation are written;
the code has been reviewed (review 5, section 12) and its three findings are fixed; the test passes;
the owner has ruled on one more point (9.4); committed on his order of 2026-11-26 11:35:37 (section 11).

## 1. What this work is

A library in Performant_Isabelle_ML with two operations on a proof context:
print a term as text, and read such text back as the same term.
The printer tries four ways of printing, from the most readable to the most explicit,
and returns the first text that it has itself read back to the same term.
When no text reads back, the printer gives up and says so.

First user: the concept system.
Sledgehammer's output for a concept fact becomes `[[concept_fact "P"]]`, where `P` is the proposition
as text; the attribute reads `P` back when the user replays the proof.
So `P` must read back to exactly the proposition the fact states.

## 2. The requirements, in the owner's words

All on 2026-11-25, UTC. The quotations are verbatim.

- 10:58:34 「我们要有多级打印。普通的打印不行了，尝试开 show_types 最后直接打印 lambda terms.
  建议做一个通用的打印器放在 Performant_ML 里，确保最后总是能读取回来.
  最后可以打印某种 elaborated raw lambda term，然后用我们自建的一个 reader 去读回来.」
- 11:04:26 「第三级还是标准的 lambda 语法，只是完全地 elaborated
  例如 "(Theory.Constant::('a,'b) Theory.Type) (x::'a)" 等，
  是标准 term reader 可读的（若所有 constants 没有被 hide），
  但我们自己实现的 reader 能够解析被 hiden 的 constants.
  在读取时，先用系统的 reader，之后再 fallback 到我们的 reader」
- 11:07:34 「在第三级的语法下，任何常量一定是全名，因此一定带有 dot，
  而变量一定不带有 dot（否则不支持，直接放弃），
  所有的 bound variables 若与其 body 内出现的 free variables 冲突，一定会被 variant」
- 11:07:34 「先用标准的 system printer，读回来发现不一样或者根本读不回来，再尝试开 show_types，再读，
  若还不行，则 fallback 到我们自己的 elaborated printing，然后用我们自己的 elaborated reader 去读，
  如果再不行就放弃」
- 11:07:34 「对不计 β-η 的差别」
- 11:11:13 「依旧建议先用系统的，且我们的 printer 满足一个特性：如果系统 reader 能读取，
  读取出来跟我们自己的 reader 读出来的应该是一样，跟 printing 前的 raw term 也是一样的
  （ignoring \beta, \eta, \alpha）」
- 12:56:12, on revision 1's point "the system reader is tried twice for a proposition":
  「这个建议设置一个参数允许用户指定是按 term 读还是按 prop 读，这样就只需要读两次了，对吗？」
- 12:56:12, on what the elaborated printer writes: 「每个新出现的 type variable 始终打印 sort.
  同一个 scope 内每个 free variable 只写一次 type annotation.
  Constant 中，如果没有多态，则不打印 type annotations」 and 「能安全地省略还是可以省略一下」.
  This replaces his 11:07:34 「我们自己的 elaborated printer 就老老实实地打印」 where the two differ.
- 12:56:12, on a text that nothing reads: 「建议返回值为 string option，用 NONE 表示无法返回」
- 12:56:12, on a `show_sorts` step: 「可以加，于是四层，original, show_types, show_sorts, custom.
  如果 original 就已经开启了 show_types/show_sorts 就对应跳过」
- 12:56:12 「不需要跟我讨论的我交给你自决」 and 「同意你一次改进计划然后送复审」.
- 15:14:37 「1. 同意 2. 同意 3. 同意」, to three questions I had put to him after review 2:
  whether the elaborated text of a proposition starts with `PROP`; whether the level Sorted turns on
  both `show_types` and `show_sorts`; whether I may change the plan again and send it to a third review.
- 15:15:36 「1. 确认 2. 确认 3. 确认 4. 确认。但对于 bound variable, 则只在 lambda binding 时打印
  type annotation」, to four points I had asked him to confirm: the name `Sorted`; that the readers
  return `term option`; that a schematic variable carries its type once, like a free variable;
  that the scope of his rule for free variables is the whole term.
- 2026-11-26 03:53:08 「1. 同意 2. 要等 compact 之后才能写」, to two questions after review 3:
  whether I may make its two fixes and run a short review; whether I may then start to write the code.
- 2026-11-26 04:37:26, after the compaction, to my three questions (may the code be written; may the
  tests run through Isabelle-MCP; shall `CONST` and `PROP` be keywords of the elaborated reader):
  「可以开始写代码了，可以用 Isabelle-MCP 也可以用 isabelle build，也可以用 REPL，都可以」 and
  「CONST 和 PROP 要做成我们 reader 的关键字」.
- 2026-11-26 05:43:42, when I asked whether I may make the three fixes of the code review:
  「不需要跟我讨论的我交给你去自主决策」.
- 2026-11-26 06:36:14, on whether a constant without a dot that is not polymorphic is written
  `(CONST name)` as the code does, or `(CONST name::type)` as his words of 12:29:24 say: 「保持现状」.
- 2026-11-26 11:35:37: 「批准提交，批准三个新增文件」.

Relayed by the session concept B from its own conversation with the owner; I have not checked its transcript:

- 12:21:52 「如果真的“命题印出来读不读得回”了，那就直接输出 Thm.dummy 让证明失败好了」 (concept side, section 10).
- 12:29:24, on four kinds of term that give up (section 7): 「这不是合法情形，可以抛弃」.
- 12:29:24, on a constant whose name has no dot:
  「所有这种不带有点的必须打印成 `(CONST name :: type)` 这样就没有问题了对吗？」
  I reported this instruction back to the owner in my session, and his go-ahead of 12:56:12 covers it.
- 12:57:06, on two more kinds of term that give up (section 7): 「算，可以放弃」.

Terms used below, each with one meaning:

- the system printer: `Syntax.pretty_term`, rendered as plain text.
- the system reader: `Syntax.read_prop` and `Syntax.read_term`.
- the elaborated syntax: the standard lambda syntax in which every constant is written by its full name,
  types are written where the reader needs them, and no notation is used (section 5).
- the elaborated printer, the elaborated reader: this library's printer and reader of the elaborated syntax.
- the four levels, by name: Plain (the system printer), Typed (with `show_types`), Sorted (with
  `show_types` and `show_sorts`), Elaborated (the elaborated printer).
  Where the quotations of 11:04:26 and 11:07:34 say 「第三级」 they mean Elaborated.
- the same term: equal up to the names of bound variables after beta-eta normalisation,
  that is `Envir.beta_eta_contract t aconv Envir.beta_eta_contract u`.
  Types, sorts, and the names and indexes of schematic variables must be equal.

## 3. What was measured (2026-11-25)

Probe: `ai-artifacts/elaborated_term_probe/` (not tracked), a prototype of the elaborated printer run in
the session HOL through Isabelle-MCP. There is no prototype of the elaborated reader.
The figures below are of the third run, whose printer follows the rules of section 5
(`corpus.out`, `cases.out`, `const_probe.out`); the earlier runs are kept in `round1/` and `round2/`.
The prototype does not write the mark `PROP` itself; the probe puts it before the text where it says so.

Corpus: 3198 propositions, every 8th of the 25579 facts of Main whose statement has term size at most 150
(Main has 25705 facts). Each proposition was tried in three situations; the table says at which level the
text first reads back to the same term through `Syntax.read_prop`:

| situation | Plain | Typed | Sorted | none of the three |
| --- | --- | --- | --- | --- |
| as stated, with schematic variables, read in `Proof_Context.mode_schematic` | 381 | 1745 | 652 | 420 |
| variables fixed in a proof body, the context does not know their types | 469 | 2310 | 0 | 419 |
| the same, and the context knows the types (`Variable.declare_term`), as for the variables of a goal | 2763 | 33 | 0 | 402 |

The third situation is the one of a concept fact about the variables of a goal: 86.4% at Plain.
What remains there are statements whose type shows only in constants, for example
`and (numeral (num.Bit1 x)) 1 = 1` and `class.canonically_ordered_monoid_add (+) 0 (≤) (<)`,
and statements with hidden names.

The elaborated text of every proposition, with `PROP` before it, read by `Syntax.read_prop`:
the same term 3124 times, failure 74 times, a different term never; identical in the three situations,
and identical to what `Syntax.read_term` does with the text, with the mark and without it.
The 74 failures:

- 31 hidden names: `Inaccessible constant` 11 times, `Inaccessible type name` 20 times.
- 43 times a constant at a type variable whose sort lacks the class that the constant's type constraint
  asks for, as in the introduction rules of classes (`Groups.plus_class.plus::'a ⇒ 'a ⇒ 'a` with
  `'a::type`): the kernel accepts such a term, the system reader's type inference does not
  (`Variable 'a::type not of sort plus`).

Facts that shape the design:

1. Under PIDE, `Pretty.unformatted_string_of` carries markup, and the text then fails to read
   (`exception XML_ATOM`). Plain text comes from `Pretty.string_of_ops (Pretty.pure_output_ops ...)`
   with `Printer.show_markup` off, which is what Sledgehammer does (sledgehammer_isar_proof.ML:410-416).
2. A failing system reader raises one of three exceptions: `ERROR`, `Par_Exn`, `Exn.EXCEPTIONS`
   (974, 219 and 186 times in the first run). Catching `ERROR` alone lets failures escape.
3. Without a mark, `Syntax.read_prop` accepts the elaborated text of none of the 3198 propositions: HOL
   reads a term at the position of a proposition as a `bool` to be wrapped in `Trueprop`, so
   `HOL.Trueprop (...)` fails with `Clash of types "prop" and "bool"`.
   With Pure's mark `PROP` before the text (pure_thy.ML:155, `PROP _`), nothing is wrapped, and
   `Syntax.read_prop` reads what `Syntax.read_term` reads: the 3124 above.
   One shape has no parse after `PROP`: a variable with its type and nothing else, `PROP (P::prop)`.
   The system printer writes that term as `PROP P`, which reads back at Plain.
4. Length in symbols, third situation: Plain has median 48, 90% 140, 99% 298;
   Elaborated has median 398, 90% 921, 99% 2329, maximum 11188. In total 7.6 times as long.
   With a type on every occurrence (first run) the median was 485.
5. Time per proposition, averaged over the corpus: system printer 0.2 ms, system reader on its text
   0.7 ms, elaborated printer 0.04 ms, system reader on the elaborated text 2 to 3 ms.
6. The system printer writes a fixed variable by its external name and a hidden constant as
   `??.Theory.name`; the latter never reads back.
7. `show_sorts` alone shows the types of variables (syntax_phases.ML:661, 758), but not the types that
   print translations add under `show_types`, such as that of a numeral (`Printer.type_emphasis`,
   printer.ML:60-63). Measured on `42 = 42 ∧ v ≤ v`, with `42` at `int` and `v` at `'a::order`:
   `show_types` gives `(42::int) = (42::int) ∧ (v::'a) ≤ v`, which fails to read;
   `show_sorts` alone gives `42 = 42 ∧ (v::'a::order) ≤ v`, which reads another term;
   both give `(42::int) = (42::int) ∧ (v::'a::order) ≤ v`, which reads back (42 symbols; Elaborated: 417).
   The column Sorted of the table above was measured with both options on.
8. `CONST` (`const_probe.out`, a constant with the full name `dotless_c` made under `Sign.root_path`):
   `Syntax.read_term` reads `(CONST dotless_c::Nat.nat)` as that constant, also where a variable named
   `dotless_c` is fixed; there the bare `(dotless_c::Nat.nat)` reads the variable.
   After `CONST` the system reader still resolves the name through the name space: a later constant
   `Const_Probe.dotless_d` is what `CONST dotless_d` finds, and a hidden constant stays inaccessible.

Single cases (`cases.out`), the elaborated text and what the system reader does with it;
`Syntax.read_prop` on the text with `PROP` and `Syntax.read_term` on the text agree in every case
except the free variable of type `prop` on its own:

| case | the elaborated text, in part | the system reader |
| --- | --- | --- |
| bound variable named `id` or `Suc` | `(λid::Nat.nat. id)` | the same term |
| bound variable with the internal name `uu_` | `(λuu::Nat.nat. ...)` | the same term |
| bound variable `y` whose body has a free `y` | `(λya::Nat.nat. (y::Nat.nat))` | the same term |
| fixed variable with internal name `x__`, twice | `(x::Nat.nat) x` | the same term |
| two fixed variables with the external name `x` | `(x__::Nat.nat) (x::Nat.nat)` | fails: `Bad name` |
| free variable `a.b` | `(a.b::Nat.nat) a.b` | fails: `Undefined constant` |
| free variable `O` (a keyword of HOL's syntax) | `(O::Nat.nat) O` | fails: `Inner syntax error` |
| free variable `id`, not fixed, of type `nat` | `(id::Nat.nat) id` | fails: clash of types (the constant `Fun.id`) |
| constant hidden by `hide_const` | `Elaborated_Probe.hidden_one` | fails: `Inaccessible constant` |
| constant hidden by `hide_const (open)` | `Elaborated_Probe.open_hidden` | the same term |
| variable `h` of a type hidden by `hide_type` | `(h::Elaborated_Probe.hidden_t) h` | fails: `Inaccessible type name` |
| `[] = []` at `nat list` (Plain, Typed, Sorted read another term) | `(List.list.Nil::Nat.nat List.list)` | the same term |
| type variable of sort `order`, used three times | `(HOL.eq::('a::Orderings.order) ⇒ 'a ⇒ HOL.bool) (a::'a) a` | the same term |
| type variable of sort `type` where the context declares `'a::order` | `('a::HOL.type)` | fails: `Sort constraint ... inconsistent with default` |
| type variable of two classes | `('a::{Groups.zero, Orderings.order})` | the same term |
| `?x1.2` and `?y3` of type `?'a1::order` | `(?x1.2::?'a1) (?y3::?'a1)` after `(?'a1::Orderings.order)` | the same term |
| monomorphic constants | `HOL.Trueprop (HOL.conj ...)`, `Pure.imp (...) (...)` | the same term |
| a schematic variable of type `nat ⇒ prop`, applied | `(?P::Nat.nat ⇒ prop) (n::Nat.nat)` | the same term |
| a free variable of type `prop`, alone | `(P::prop)` | `Syntax.read_term`: the same term; with `PROP`: no parse |
| a beta redex, an eta redex, `TYPE(nat)`, numerals, strings, a set comprehension, `⋀` with `⟹` | | the same term |

Two full examples, with their lengths in symbols.
`monoid f z` (10) is `PROP HOL.Trueprop ((Groups.monoid::(('a::HOL.type) ⇒ 'a ⇒ 'a) ⇒ 'a ⇒ HOL.bool)
(f::'a ⇒ 'a ⇒ 'a) (z::'a))` (105).
`(v = v) ∧ (v ≤ v)` at `'a::order` is `PROP HOL.Trueprop (HOL.conj ((HOL.eq::('a::Orderings.order) ⇒ 'a ⇒
HOL.bool) (v::'a) v) ((Orderings.ord_class.less_eq::'a ⇒ 'a ⇒ HOL.bool) v v))` (144).
The lengths of fact 4 do not count the five symbols of `PROP` and its space.

## 4. The interface

One file, `library/roundtrip_syntax.ML`, loaded by `Performant_Isabelle_ML.thy`.
It needs Pure only, and nothing else of this repository except `Interrupt_Family` (section 6).

```ML
signature ROUNDTRIP_SYNTAX =
sig
  datatype level = Plain | Typed | Sorted | Elaborated
  val string_of_term: Proof.context -> term -> (level * string) option
  val string_of_prop: Proof.context -> term -> (level * string) option
  val read_term: Proof.context -> string -> term option
  val read_prop: Proof.context -> string -> term option
  val string_of_elaborated: Proof.context -> term -> string
  val read_elaborated: Proof.context -> string -> term
end
```

- [owner 12:56:12] The names of the file, the structure, the six functions, and `Plain`, `Typed`, `Elaborated`.
- [owner 15:15:36] `Sorted`, the name of the level he added at 12:56:12.
- [owner 12:56:12, 15:15:36] The two readers return `term option`, `NONE` when nothing reads the text.

The contract. In both lines `u` is the same term as `t`, at every level.

| printed by | read by |
| --- | --- |
| `string_of_term ctxt t = SOME (_, s)` | `read_term ctxt s = SOME u` |
| `string_of_prop ctxt t = SOME (_, s)` | `read_prop ctxt s = SOME u` |

[owner 12:56:12] The caller says whether a text is read as a term or as a proposition, by calling
`read_term` or `read_prop`; each then reads at most twice (section 6).
`NONE` from a printer means it gave up.

The context of printing and the context of reading are the caller's to keep equal:
the same fixed variables, the same declared types and sorts, the same theory and mode,
and the same term bindings (`?thesis`, `let ?x = ...`).
Both readers replace a schematic variable that the context binds by the term bound to it
(proof_context.ML:711-725, variable.ML:294-298; 5.3). A caller whose terms carry schematic variables of their
own hands both the printer and the reader a context without the bindings:
`Vartab.fold (Variable.unbind_term o #1) (Variable.binds_of ctxt) ctxt`.
The term handed to a printer has no loose bound variable.

[design] All three readers take inner syntax in the form `Syntax.read_term` takes it: plain text, or
`Syntax.implode_input` of a source, which is what Isar hands to an attribute or a command.
The printers return plain text.

`string_of_prop` and `read_prop` are for a term of type `prop`; `string_of_term` and `read_term` for a
term of any type. `string_of_elaborated` and `read_elaborated` are Elaborated alone, without any check.

## 5. The elaborated syntax

### 5.1 What the elaborated printer writes

The text is written from left to right, and "first occurrence" means the first in the text.

The mark of a proposition:

- [owner 15:14:37] The text of a term of type `prop` starts with `PROP ` (fact 3 of section 3).
  [design] The test is the type of the whole term and nothing else; no other `PROP` is ever written.
  An elaborated text never starts with a bare `id`, so the mark cannot be taken for a variable.

Constants:

- [owner 11:07:34] A constant is written by its full name.
- [owner 12:29:24, relayed] A constant whose name has no dot is written `CONST name`.
- [owner 12:56:12] A constant that is not polymorphic carries no type: `HOL.Trueprop`.
- [owner 2026-11-26 06:36:14] This holds for a constant without a dot too: it is written `(CONST name)`,
  without a type, although his words of 12:29:24 were `(CONST name :: type)`.
  I had merged his two statements in this way without telling him (9.4).
- [design] Not polymorphic means: its declared type has no type variable.
  The declared type is looked up in the context's table of constants
  (`Consts.type_scheme (Proof_Context.consts_of ctxt)`), the table certification uses; it knows
  abbreviations too, which `Sign.const_type` does not (review 5).
  A constant is written without a type only at its declared type; at any other type the type is
  written, and certification then refuses the text.
- [owner 11:04:26] Any other constant carries its type at every occurrence: `(c::T)`, `(CONST name::T)`.

Variables:

- [owner 12:56:12, 15:15:36] A free variable carries its type once in the whole term:
  `(x::T)` at its first occurrence, `x` afterwards.
  [design] For a fixed variable the name written is its external name, `Proof_Context.extern_fixed ctxt x`,
  which is what the system printer writes.
- [owner 15:15:36] A schematic variable is treated like a free variable: `(?x::T)` first, `?x` afterwards.
  [design] The name is written by `Term.string_of_vname`.
- [owner 15:15:36] A bound variable carries its type at its binder only;
  an occurrence is written as the bare name chosen for the binder.
- [owner 11:07:34] An abstraction `Abs (x, T, b)` is written `λx::T. b`, the name changed when it clashes
  with a free variable of the body.
  [owner 12:56:12 「好的」] The name chosen is `Name.variant` of the cleaned name against the written names
  of all free variables of the whole term and the names chosen for the enclosing binders.
  The cleaned name is `Name.clean x`; when that is not an identifier, the name `"x"` is taken instead.
  Cleaning turns `uu_`, the name the system gives to `λ_. t`, into `uu`, which the system reader accepts.
  [design] The names `CONST` and `PROP` are avoided as well: both are keywords of the reader (5.2),
  so a binder of either name could not be read.

Types:

- [owner 12:56:12] A type variable carries its sort once, and always: `('a::S)` at its first occurrence,
  `'a` afterwards. `S` is `c` or `{c1, c2}` or `{}`, classes by their full names.
  No default sort is consulted anywhere, neither the theory's nor the context's.
- [design] A function type is written `T ⇒ U`, the left side parenthesised when it is a function type.
  Any other type is written postfix by the full name of its constructor: `Nat.nat`, `Nat.nat List.list`,
  `(Nat.nat, HOL.bool) Product_Type.prod`.

The rest:

- [design] An application is written `f a b`; an argument that is an application or an abstraction is
  parenthesised, and so is an abstraction in the position of the function.
- [design] The symbols are `\<lambda>` and `\<Rightarrow>`.
- There is no notation, no abbreviation, and no normalisation: a redex is written as a redex.

[design] One rule covers a term that uses one name at two types, or one type variable at two sorts:
the printer keeps the two tables the reader keeps (5.3), and writes an occurrence bare exactly when the
table already holds this type for the name, or this sort for the type variable.
For any other term this is the first-occurrence rule above.

### 5.2 The grammar the elaborated reader accepts [design]

```
top   ::= "PROP" term | term
term  ::= app | "λ" id "::" type "." term
app   ::= atom | app atom
atom  ::= id | var | longid
        | "(" name "::" type ")" | "(" "CONST" id ")" | "(" term ")"
name  ::= longid | "CONST" id | id | var
type  ::= tapp | tapp "⇒" type
tapp  ::= tatom | tapp tname | "(" type "," type { "," type } ")" tname
tatom ::= tname | tvar | "(" tvar "::" sort ")" | "(" type ")"
tname ::= longid | id
tvar  ::= tid | tvar-token
sort  ::= cname | "{" [ cname { "," cname } ] "}"
cname ::= longid | id
```

The text is cut into tokens by Isabelle's own tokenizer, in the way `Simple_Syntax` does it
(Pure/Syntax/simple_syntax.ML:19-29), which is also the system reader's tokenizer:

- the symbols are obtained the way Isabelle obtains them (syntax_phases.ML:490-492):
  `Syntax.read_input s |> Input.source_explode`; so plain text and the encoded form give the same symbols;
- `Lexicon.tokenize lexicon {raw = false}`, then `filter Lexicon.is_proper`,
  then the parser by `Scan.read Lexicon.stopper`;
- the lexicon holds `(`, `)`, `::`, `.`, `,`, `{`, `}`, `\<lambda>`, `\<Rightarrow>`,
  and the two keywords `CONST` and `PROP` [owner 2026-11-26 04:37:26];
- the parser works on `Lexicon.token`; `id`, `longid`, `var`, `tid` and the schematic type variable are
  the kinds `Ident`, `Long_Ident`, `Var`, `Type_Ident`, `Type_Var` of `Lexicon.kind_of_token`.

A lexical error of the tokenizer is reported like any text outside the grammar (5.3).
`CONST` and `PROP` are keywords: the tokenizer never returns either word as an `id`, so no rule of
the grammar has to look at the neighbouring tokens. Isabelle's own lexicon has both as keywords too.
The reader accepts what the printer writes; it is not a second reader for hand-written terms.

### 5.3 What the elaborated reader builds

The reader goes through the text from left to right and keeps two tables:
the type last written for each variable name, and the sort last written for each type variable.

- [owner 11:07:34] A `longid` is a constant, by that full name. A name with a dot is a constant.
- [owner 12:29:24, relayed] `CONST x` is the constant with the full name `x`.
- [design] A constant written without a type gets its declared type, which must have no type variable.
- [owner 11:07:34] An `id` is a variable. A name without a dot is a variable.
  [design] `(x::T)` enters `T` for `x` in the table. A bare `x` is the innermost enclosing binder of that
  name; without one, the free variable `x` at the type the table holds; without that, the reader fails.
  [design] The free variable built is `Free (x', T)`, `x'` the internal name when `x` is fixed in the
  context (`Variable.lookup_fixed ctxt x`), else `x`. This inverts `Proof_Context.extern_fixed`.
- [design] `(?x::T)` and a bare `?x` likewise. The indexname of a `Var` or `Type_Var` token is
  `Lexicon.read_indexname o unprefix "?"`, as at simple_syntax.ML:47.
- [design] A type name is the full name of a type constructor. `('a::S)` enters `S` for `'a` in the table;
  a bare `'a` gets the sort the table holds; without one the reader fails.
- [design] The result is finished in the context, in two steps:
  `Proof_Context.cert_prop ctxt` after the mark `PROP`, `Proof_Context.cert_term ctxt` otherwise
  (proof_context.ML:894-905); then `singleton (Proof_Context.standard_term_check_finish ctxt)` (:919).
  The system reader ends in the same two: its check phases are type inference with
  `Proof_Context.expand_abbrevs` (stage 0) and `standard_term_check_finish` (stage 100)
  (syntax_phases.ML:1041-1044). `cert_term` is `expand_abbrevs` followed by `Sign.certify_flags`, which
  stands in for the checks that type inference makes.
  So, as far as Pure's standard check phases go, the two readers differ in two things only:
  how a name is resolved, and that the elaborated reader infers no type.
  A theory may register check phases of its own (HOL does, for ad-hoc overloading and for case
  expressions); they act on things the proposition of a theorem does not contain.
  - A constant that is not declared, a type that is not an instance of the declared one, a type
    constructor of the wrong arity, an unknown class, a text marked `PROP` that is not of type `prop`:
    all fail.
  - Hidden names pass: certification looks a constant up by its full name (consts.ML:106-111).
    A constant at a sort that lacks its class passes: `Type.raw_instance` ignores sorts (consts.ML:194).
  - Abbreviations, term bindings and the mode mean what they mean to the system reader: a schematic
    variable that the context binds is replaced by the term bound to it (proof_context.ML:710-727);
    outside `Proof_Context.mode_schematic` and `mode_pattern` a schematic variable fails, and so does a
    schematic type variable (`prepare_patternT`, :756-766).
  - The term returned is beta-normal outside `mode_pattern` (`Variable.expand_binds`, variable.ML:294-298).

Every failure of the elaborated reader is an exception.
[owner 12:56:12 「按你建议来」] For a text that is not in the grammar `read_elaborated` raises
`ERROR "Malformed elaborated term: <the text, quoted>"`; the text quoted is the plain content of the
symbols. A user never meets this through `read_term` or `read_prop`, which return `NONE`.

## 6. The reader

[owner 11:04:26] The system reader first, the elaborated reader second.

`read_term ctxt s`:

1. `Syntax.read_term ctxt s`; when it returns a term, that is the result.
2. If that fails: `read_elaborated ctxt s`.
3. If that fails too: `NONE`.

`read_prop ctxt s`:

1. `Syntax.read_prop ctxt s`.
2. If that fails: `read_elaborated ctxt s`, accepted when its type is `prop`.
3. If that fails too: `NONE`.

[design] To fail means to raise an exception that is not an interrupt.
The test is `Interrupt_Family.contains_interrupt` (library/accounted_timeout.ML), as in library/race.ML:
a `Par_Exn` may carry an interrupt, and the system reader does raise `Par_Exn` (fact 2).
An interrupt is raised again.

The exception of the system reader is not kept.
A caller that wants its message for the user calls the system reader once more.

## 7. The printer

[owner 12:56:12] Plain, then Typed, then Sorted, then Elaborated; the first text that reads back to the
same term; else give up.

- Plain: `Syntax.pretty_term` in the context with `Printer.show_markup` off, rendered by
  `Pretty.string_of_ops (Pretty.pure_output_ops (SOME m))` with a margin `m` so large that no line breaks.
- Typed: the same with `show_types` on.
  [owner 12:56:12] Skipped when the context already has `show_types` on.
- Sorted: the same with `show_types` and `show_sorts` on [owner 15:14:37]; `show_sorts` alone would
  write fewer types than Typed (fact 7).
  [owner 12:56:12] Skipped when the context already has `show_sorts` on.
- Elaborated: `string_of_elaborated ctxt t`.

A level that is skipped would print in exactly the options of an earlier level, so a skip never loses a
text: with `show_types` on, Typed is Plain; with `show_sorts` on, Sorted is Typed, or Plain when
`show_types` is on as well.

No other option of the context is touched: abbreviations, notation and the like are the caller's.

[owner 12:56:12 「好」] The check is the library's own reader, the one the contract of section 4 names:
`read_term` for `string_of_term`, `read_prop` for `string_of_prop`.
It is run on the text, in the context with `Context_Position.set_visible false` so that
no warning and no report is emitted, and the text is accepted when it returns the same term.
A reader that returns `NONE` rejects the text like a reader that returns another term.

[owner 12:56:12 「好」] At Elaborated one more condition: `read_elaborated` alone returns the same term.
So an elaborated text does not depend on the system reader being able to read it.

What this gives, since the check is the reader itself:

- An accepted text reads back to the same term: the contract of section 4, by construction.
- [owner's property of 11:11:13] For an accepted elaborated text, the system reader either fails or
  returns the same term: if `Syntax.read_prop` returned another term, `read_prop` would return that term,
  and the text would have been rejected; likewise `Syntax.read_term` and `read_term`.
  And the elaborated reader returns the same term.
- [owner 11:04:26: 「是标准 term reader 可读的（若所有 constants 没有被 hide）」] With the mark `PROP` this holds
  for a proposition read as a proposition: in the corpus, for all but hidden names and the terms that the
  system's type inference rejects (section 3).

Giving up needs no test of its own: a term gives up when its elaborated text does not pass the check.
[owner 12:29:24, relayed: 「这不是合法情形，可以抛弃」] Nothing is built for these four:

- a free or schematic variable with a dot in its name (the elaborated reader takes it for a constant);
- a free variable whose name is not an identifier of the lexicon;
- a free variable, not fixed, whose name is the external name of a fixed variable (both are written by
  that name, and every reader maps the name to the fixed one);
- a term with a loose bound variable (excluded by the contract, not by the check).

[owner 12:57:06, relayed: 「算，可以放弃」] Nor for these two:

- a free variable, neither fixed nor declared in the context, named like an accessible constant of a
  fitting type: the system reader returns the constant. No standard syntax marks a name as a variable.
  For the variables of a goal it does not arise.
- a term that certification changes, such as one with an unexpanded abbreviation: the two readers
  end alike (5.3), and both return what certification makes of the term.
  The proposition of a theorem is never such a term.

Two more kinds give up:

- a free variable named `CONST` or `PROP`: both words are keywords of the elaborated reader
  [owner 2026-11-26 04:37:26] and of the system reader, so no reader reads such a variable;
- a schematic variable that the context binds as a term binding: every reader returns the term bound to
  it, at every level (5.3). The caller avoids this by the context it hands in (section 4).

A constant without a dot no longer gives up: it is written with `CONST`.

Cost, by the figures of fact 5 and not measured as a whole: a term accepted at Plain costs one print and
one read, about 1 ms. A term that reaches Elaborated costs three rejected levels, about 1 ms each, and one
reading of the elaborated text by the system reader: about 6 ms.

## 8. Tests

`Test/Roundtrip_Syntax_Test.thy`, importing `Main` and `"../Performant_Isabelle_ML"`,
run by hand like every test of this repository (none is in ROOT). A failure is an `error`.

1. The elaborated printer and reader on hand-built terms, one per production of 5.2 and per rule of 5.1
   and 5.3: the text is compared literally, and `read_elaborated` returns the same term.
   Each text is read twice: as plain text, and as `Syntax.implode_input (Input.string s)`.
   A term with a schematic variable or a schematic type variable is read in `mode_schematic`.
2. Single cases, each with the level expected from `string_of_prop` (or `NONE`), and the reader of the
   contract returning the same term, again in both input forms:
   - a hidden constant: `Elaborated`;
   - `h = h` with `h` of a hidden type that the context does not declare: `Elaborated`;
     `h = HT` with the constructor `HT` of that type: `Plain`;
   - a constant at a type variable whose sort lacks the class: `Elaborated`;
   - two fixed variables with one external name: `Elaborated`;
   - a type variable of sort `type` where the context declares `'a::order`: `Elaborated`;
   - a constant without a dot: `Plain`; where a variable of its name is fixed: `Elaborated`;
   - `?x1.2 = ?y3` at the type `?'a1::order`, in `mode_schematic`: `Sorted` (measured);
   - the same in a context with `show_types` on: `Sorted`, and `Typed` is never returned there;
     the same in a context with `show_sorts` on: `Plain`;
   - `42 = 42 ∧ v ≤ v` with `42` at `int` and `v` at `'a::order`, `v` not fixed: `Sorted` (fact 7);
   - `(42, ''ab'') = (42, ''ab'')` with `42` at `int`, in a context with `show_sorts` on: `Typed`;
   - `[] = []` at `nat list`: `Elaborated`, and `Syntax.read_prop` alone returns the same term from the
     text, which shows that the mark `PROP` is written and works;
   - `?P` of type `prop` in a context that binds `?P`, in `mode_schematic`: `NONE`;
     `Plain` once the bindings are removed, still in `mode_schematic`;
   - `UNIV ≠ {}` at `?'a set`, in the default mode: `NONE` (no reader accepts a schematic type variable
     there);
   - a free variable with a dot: `NONE`; a free variable named like a constant of a fitting type, neither
     fixed nor declared: `NONE`; a free variable with the external name of a fixed variable: `NONE`;
   - a free variable named `CONST`: `NONE`; one named `PROP`: `NONE`;
   - a bound variable named `CONST` or `PROP`: the binder is written `CONSTa` or `PROPa`.
   For `string_of_term`, read back by `read_term` in both input forms:
   - `[]` at `nat list`: `Elaborated` (every system level prints `[]`, which reads at `'a list`);
   - a hidden constant on its own: `Elaborated`;
   - `x + y` with `x` and `y` fixed and declared at `nat`: `Plain`.
3. The corpus of section 3 in its three situations: `string_of_prop` returns `SOME` for every proposition,
   the reader of the contract returns the same term, and for every proposition `read_elaborated` returns
   the same term from `string_of_elaborated`. The counts per level are compared with section 3.
   That every proposition of the corpus gets a text was the expectation; the probe had no elaborated reader.
   Measured with the code on 2026-11-26: every proposition gets a text (section 11).
4. `read_prop` and `read_term` return `NONE` on a text that nothing reads, and read a hand-written text.
5. A check by mutation, kept short. Each of these must make a test fail: write no sort at a first
   occurrence; write a polymorphic constant bare; do not rename a bound variable; write a fixed variable
   by its internal name; catch `ERROR` only; explode the raw string instead of the input;
   leave out the mark `PROP`; print Sorted with `show_sorts` alone; check `string_of_term` with `read_prop`;
   certify with `Sign.certify_term` instead of in the context; leave out `standard_term_check_finish`.
   Added with the code and after review 5: take `CONST` and `PROP` out of the lexicon; read a bare
   variable under a binder of its name as the free variable; replace the test for interrupts by
   Isabelle's `try`; ask `Sign.const_type` whether a constant is polymorphic.

## 9. Decisions

### 9.1 Ruled by the owner on 2026-11-25 12:56:12, on the ten points of revision 1

1. The names: 「赞同」.
2. The system reader twice for a proposition: replaced by the caller's choice of term or proposition
   (section 4), and after review 2 by the mark `PROP` (9.2).
3. The sort of a type variable, and 8. the type on every occurrence: replaced by his three rules (5.1).
4. The check is the library's own reader: 「好」.
5. A text that nothing reads: no exception, `NONE`; the type is `term option` (confirmed, 9.2).
6. Bound variables renamed against all free variables and enclosing binders, internal names cleaned: 「好的」.
7. A `show_sorts` step: added, with the two skips (section 7).
9. The text of the error of `read_elaborated`: 「按你建议来」.
10. Readme.md and SKILL.md get one entry; VERSION is not touched; CHANGELOG is mine to decide.
    I add an entry to CHANGELOG with the code.

### 9.2 Ruled by the owner after review 2

- 15:14:37: the elaborated text of a proposition starts with `PROP` (5.1); Sorted turns on both
  `show_types` and `show_sorts` (section 7).
- 15:15:36: the name `Sorted`; the readers return `term option`; a schematic variable carries its type
  once, like a free variable; the scope of his rule for free variables is the whole term; a bound
  variable carries its type at its binder only.

### 9.3 Ruled by the owner on 2026-11-26 04:37:26

The question, raised by review 3: shall `CONST` and `PROP` be keywords of the elaborated reader,
that is, entries of the lexicon of 5.2? His answer: 「CONST 和 PROP 要做成我们 reader 的关键字」.

- The two rules of revision 5 that looked at neighbouring tokens are gone (5.2).
- Binders avoid the name `PROP` as they avoid `CONST` (5.1).
- A free variable named `CONST` or `PROP` always gives up (section 7). Isabelle's own lexicon has
  both words as keywords, so the system reader reads no variable of either name anyway.

### 9.4 Ruled by the owner on 2026-11-26 06:36:14

The session concept B found that revision 6 labelled as the owner's a point he had not been told of:
his words of 12:29:24 (relayed) ask for `(CONST name :: type)`, his rule of 12:56:12 takes the type
off every constant that is not polymorphic, and the code applies the later rule to a constant
without a dot as well: `(CONST name)`.

- The difference in effect: with the type, a text still reads back where a later constant with a
  dot has the same base name and a type that fits the place; without it that term gets `NONE`.
  Neither form ever reads back another term.
- I recommended to write the type. His ruling: 「保持现状」, so `(CONST name)` stays.

Every other point labelled [design] is a detail of how his rules are carried out.

## 10. Not part of this work

- The cache key `[[concept_fact "P" key]]` and the proof store.
- The concept side: which context is handed to the printer and to the reader, with or without the term
  bindings of the proof; how the text is quoted in `[[concept_fact "P"]]`; the trigger's interface; and
  what becomes of a fact whose proposition gives up (the owner's ruling of 12:21:52, relayed).
- Any notation of the concept system.

## 11. Steps

The state of 2026-11-26 04:40 UTC, after the compaction of the session:

- The plan has had four reviews (section 12). The one finding of the fourth is written in; the owner
  has been told of it, and no fifth review has been run.
- [owner 2026-11-26 04:37:26] The code may be written. The tests may run through Isabelle-MCP,
  through `isabelle build`, or through the REPL, as I choose.
- The session concept B writes the first user (`contrib/concept/concept_fact.ML`) and has the interface
  of section 4. It has been told that both readers end alike (5.3). The owner ruled for its side
  (2026-11-26 03:55:05, relayed) that a user's `?thesis` in `[[concept_fact "P"]]` means the binding, so
  it hands in the context with its term bindings and renames the schematic variables of the
  propositions it prints away from them.

The steps:

1. Done: `library/roundtrip_syntax.ML` and its line in `Performant_Isabelle_ML.thy`.
2. Done: `Test/Roundtrip_Syntax_Test.thy`.
3. Done: the entry in Readme.md, in SKILL.md and its copy `.claude/skills/performant-isabelle-ml/SKILL.md`
   (the three files are identical), and in CHANGELOG.md under "Unreleased".
4. Done: code review (review 5, section 12); its three findings are fixed in the code, the test and
   the documentation, on the owner's word of 2026-11-26 05:43:42 that matters needing no discussion
   are mine to decide (「不需要跟我讨论的我交给你去自主决策」).
5. Done: the commit, on the owner's order of 2026-11-26 11:35:37 (「批准提交，批准三个新增文件」), with
   the three new files (the library file, the test theory, this plan) that he approved in those words.

What the test measured (2026-11-26, session HOL through Isabelle-MCP, no `isabelle build`):

- The test theory has five parts: the elaborated syntax rule by rule (tests 1 of section 8); what
  `read_elaborated` refuses and how it finishes a term (tests 1 and 2); single terms with the level
  expected (test 2); the two readers on hand-written text (test 4); the corpus (test 3).
  All parts pass, without a warning.
- The corpus is every 8th fact of the theory Main alone with term size at most 150: 3194 propositions
  (the probe's 3198 included the facts of the probe theory, so the sample is another one).
  In each of the three situations every proposition gets a text from `string_of_prop` that `read_prop`
  reads back to the same term, and `read_elaborated` reads back `string_of_elaborated`.

  | situation | Plain | Typed | Sorted | Elaborated | time for the 3194 |
  | --- | --- | --- | --- | --- | --- |
  | as stated, with schematic variables, in `mode_schematic` | 367 | 1735 | 650 | 442 | 10.0 s |
  | variables fixed, the context does not know their types | 476 | 2278 | 0 | 440 | 9.4 s |
  | the same, and the context knows the types | 2749 | 29 | 0 | 416 | 6.5 s |

  The times include the test's own second reading of every text: 2 to 3 ms per proposition.
- Speed and length per level, measured on the same sample with the code
  (`ai-artifacts/roundtrip_syntax_mutation/Speed_Probe.thy`, not tracked; each reading is the least of
  three runs). Per level: its share, the time of `read_prop` on the text returned, the time of
  `string_of_prop` (all levels tried and checked), and the symbols of the text returned divided by the
  symbols of the Plain text of the same propositions.

  | situation | level | share | `read_prop` | `string_of_prop` | length / Plain |
  | --- | --- | --- | --- | --- | --- |
  | fixed, types known | Plain | 86.0% | 0.57 ms | 0.84 ms | 1.00 |
  | | Typed | 0.9% | 0.53 ms | 1.76 ms | 1.36 |
  | | Elaborated | 13.0% | 0.83 ms | 2.46 ms | 7.75 |
  | | all | | 0.60 ms | 1.06 ms | 1.66 |
  | fixed, types unknown | Plain | 14.9% | 0.37 ms | 0.59 ms | 1.00 |
  | | Typed | 71.3% | 0.84 ms | 2.30 ms | 1.69 |
  | | Elaborated | 13.7% | 0.89 ms | 2.77 ms | 7.63 |
  | | all | | 0.78 ms | 2.11 ms | 2.25 |
  | schematic | Plain | 11.4% | 0.42 ms | 0.67 ms | 1.00 |
  | | Typed | 54.3% | 0.98 ms | 2.70 ms | 1.74 |
  | | Sorted | 20.3% | 0.56 ms | 2.38 ms | 2.01 |
  | | Elaborated | 13.8% | 0.93 ms | 2.92 ms | 7.47 |
  | | all | | 0.82 ms | 2.43 ms | 2.31 |

  On the elaborated text of every proposition, `read_elaborated` alone takes 0.09 to 0.10 ms and
  `Syntax.read_prop` 1.4 to 1.5 ms; the latter reads 3090 of the 3194.
  Of the 416 propositions at Elaborated in the first situation, `Syntax.read_prop` reads 338.
  Per proposition, the elaborated text is 8.7 times the Plain text in the median
  (`Length_Probe.thy` beside the other probe).
- The check by mutation (test 5) was run on a copy of the library
  (`ai-artifacts/roundtrip_syntax_mutation/make_mutant.py`, not tracked): each of the 11 mutations
  first listed in section 8 makes the test fail, and so does each of the four added there.
  One more mutation passes the test: "the elaborated text is not checked with `read_elaborated`
  alone". No known term decides that second condition of section 7, since `read_term` and
  `read_prop` fall back to `read_elaborated`; review 5 ruled to keep the condition, which makes
  "an accepted elaborated text does not depend on the system reader" true by construction.
  After the fixes of review 5 the mutations whose text changed, and the two new ones, were run again.

Details of carrying out the rules that the sections above do not state (review 5 found them sound):

- A constant written without a type that is not declared, or that is polymorphic, is reported as a
  malformed text.
- Failures of building (a bare variable without a type in the table, a bare type variable without a
  sort) raise the same error as a text outside the grammar.
- The grammar in the code is left-factored; the language is the one of 5.2.
- An exception of the system printer or of the elaborated printer is not caught; the contract
  excludes the one known cause, a loose bound variable.

## 12. Record of reviews

Review 1 (revision 1, 2026-11-25; report `ai-artifacts/roundtrip_syntax_review/review1_2026-11-25.md`):
three findings upheld, none for the owner.

- A. The plan did not say how the elaborated reader obtains its symbols; Isar hands an attribute the
  encoded form of the text, which a reader exploding the raw string cannot read, so a text that only the
  elaborated reader reads would pass the check and fail at replay.
  Fixed: the input form in sections 4 and 5.2, the second reading in tests 1 and 2, one mutation in test 5.
- B. The rule for leaving out a sort named the theory's default sort where the system reader uses the
  context's. Dissolved by the owner's rule of 12:56:12: the sort is always written at the first
  occurrence, and no default sort is consulted (5.1, 5.3).
- C. Test 2 expected `Elaborated` for `h = HT`, which reads back at `Plain`.
  Fixed: `h = h` expects `Elaborated`, `h = HT` expects `Plain`.

Review 2 (revision 2, 2026-11-25; report `ai-artifacts/roundtrip_syntax_review/review2_2026-11-25.md`):
it confirmed from the sources that the system reader gives a bare later occurrence the type or the sort
written at the first one, wherever the first one stands. Four findings upheld, one rejected.

- 1. Revision 2 let the caller read the elaborated text of a proposition as a term, with a third line in
  the contract and a second reading in the check, because `Syntax.read_prop` rejects that text.
  The review proposed Pure's mark `PROP` instead. Measured (fact 3), put to the owner, agreed 15:14:37.
  Done: 5.1, 5.2, 5.3, the contract of section 4, the check and the cost of section 7, tests 2 and 5.
- 2. Rejected: to replace the two skips by "skip a level whose text equals an earlier one".
- 3. Fact 7 was false for the printed text, and the skip of Typed went beyond the owner's words.
  Fixed: fact 7, Sorted with both options (agreed 15:14:37), the two skips in his words, tests 2 and 5.
- 4. A schematic variable that the context binds was not named among the terms that give up.
  Fixed, in words only: sections 4, 7 and 10, and one case in test 2.
- 5. No test called `string_of_term`. Fixed: three cases in test 2 and one mutation in test 5.

Review 3 (revision 3, 2026-11-25; report `ai-artifacts/roundtrip_syntax_review/review3_2026-11-25.md`):
it found the mark `PROP` sound and the plan ready to implement once two findings are fixed.

- 1. The elaborated reader certified at the level of the theory (`Sign.certify_term`), so it ignored the
  term bindings and the mode of the context: a schematic variable that the context binds was replaced
  by the system reader and kept by the elaborated reader, and test 2 expected what the design did not do.
  Fixed: certification in the context (5.3), the wording of sections 4 and 7, tests 1, 2 and 5.
- 2. The plan named five scanners and not how they are combined, and a function that cannot take the
  token of a schematic variable. Fixed: the pipeline of `Lexicon.tokenize` and the indexname (5.2, 5.3).
- An optional proposal, `CONST` and `PROP` as keywords: adopted by the owner on 2026-11-26 (9.3).

Review 4 (revision 4, 2026-11-26, one reviewer; report
`ai-artifacts/roundtrip_syntax_review/review4_2026-11-26.md`): the tokenizer is right; one finding.

- The certification of review 3 copied only the first of the system reader's two check stages, so the
  elaborated reader accepted a schematic type variable outside `mode_schematic`, where the system reader
  rejects it. Fixed: `Proof_Context.standard_term_check_finish` after certification (5.3), the wording
  of 5.3 and section 7, tests 1, 2 and 5.

Review 5 (the code, 2026-11-26, two reviewers; report
`ai-artifacts/roundtrip_syntax_review/review5_code_2026-11-26.md`): the code carries out the plan; no
term was found whose text does not read back, no interrupt that is swallowed. Three findings, none
for the owner, all fixed.

- 1. No test showed that an interrupt is raised again: Isabelle's `try` in place of the library's
  own test would have passed, and `try` takes a `Par_Exn` that carries an interrupt for a failure.
  Fixed: a test whose context raises such an exception while reading, and one line of comment.
- 2. The header comment said that a schematic variable named `CONST` or `PROP` gets `NONE` (it reads
  back; only a free variable of those names does not), and did not tell a caller whose term has
  schematic variables of its own to print and read in `mode_schematic`.
  Fixed, in words: the header, the warning in Readme.md and SKILL.md, the header of the test.
- 3. Whether a constant is polymorphic was asked of `Sign.const_type`, which knows no abbreviation,
  so an abbreviation without type variables was written with its type, against the owner's rule.
  Fixed: `Consts.type_scheme` on the context's constants (5.1), and one test.
