(* Generic collections of items indexed by an iNet discrimination net.

   Two layers.  `iNet_Collection' stores ANY element type in a `Generic_Data'
   slot; `iNet_Thm_Collection' specialises it to theorems and adds what
   `Named_Thms' (Pure/Tools/named_thms.ML) provides: an add/del attribute and a
   dynamic fact name.

   THE KEY FUNCTION IS PART OF THE MODEL.  `key_of' declares what question the
   net answers.  For the same theorems, keying on the full proposition answers
   "which stored statements look like this" (`Named_Thms' semantics); keying on
   the left-hand side of a meta-equation answers "which rules can fire on this
   subterm" (rewrite-rule semantics).  A collection without a key notion would
   be a plain list filed under an iNet's name.

   KEY SEMANTICS ARE NOT TYPE-CHECKED.  A net whose keys are not rule left-hand
   sides type-checks against `Merely_Rewrite.rewrite_conv' and silently
   rewrites nothing it should.  Handing a consumer a net built with the key
   function that consumer assumes is the instance's responsibility.

   `eq' IS ONE PARAMETER SHARED BY insert, delete AND merge.  The thm layer
   pins `Thm.eq_thm_prop' (prop + tpairs; coarser than `Thm.eq_thm', which
   additionally compares hyps and shyps -- neither predicate looks at
   certificates, so trimming never affects equality).  A mixed-predicate merge
   shows up as duplicate entries when same-prop rules differ in hyps/shyps.

   SAME KEY: THE LATER ADDITION COMES FIRST, so a consumer taking the first
   match sees the later declaration win.  This is iNet's documented lookup
   order ("Lookup functions preserve order in items stored at same level",
   improved_net.ML) and holds within a single theory; the relative order of
   same-key items merged from different theories depends on the import
   direction.  `content' order carries no guarantee at all.

   There is no counterpart of `Item_Net.member': no consumer needs it today.

   Instances should raise a descriptive TERM/THM from `key_of' when rejecting
   an input: a bare `Logic.dest_equals' key surfaces to the user as
   `<name>: dest_equals'.
*)

signature INET_COLLECTION =
sig
  type T
  val get_net: Context.generic -> T iNet.net   (*the net itself -- the key-semantics warning in the header applies*)
  val content: Context.generic -> T list
  val add: T -> Context.generic -> Context.generic
  val del: T -> Context.generic -> Context.generic
end;

functor iNet_Collection(
  type T
  val eq: T * T -> bool        (*ONE predicate for insert, delete and merge -- see header*)
  val key_of: T -> term
): INET_COLLECTION =
struct

type T = T;

structure Data = Generic_Data
(
  type T = T iNet.net;
  val empty = iNet.empty;
  val merge = iNet.merge eq;
);

val get_net = Data.get;
val content = iNet.content o Data.get;
fun add x = Data.map (iNet.insert_term_safe eq (key_of x, x));
fun del x = Data.map (iNet.delete_term_safe eq (key_of x, x));

end;


(*The thm layer follows named_thms.ML:18-43 line by line.  Three things are
  new: the `key_of'' wrapping, `get_net', and exporting `content' (`NAMED_THMS'
  keeps it private, only feeding it to `add_thms_dynamic'; here the same outlet
  is open to ML consumers).  The two outlets deliberately differ: `get_net'
  hands out the stored, context-free entries; `content'/`get' transfer them
  into the caller's context first.*)

signature INET_THM_COLLECTION =
sig
  val get_net: Proof.context -> thm iNet.net
  val content: Context.generic -> thm list
  val get: Proof.context -> thm list
  val add_thm: thm -> Context.generic -> Context.generic
  val del_thm: thm -> Context.generic -> Context.generic
  val add: attribute
  val del: attribute
  val setup: theory -> theory
end;

functor iNet_Thm_Collection(
  val name: binding
  val description: string
  val key_of: thm -> term
): INET_THM_COLLECTION =
struct

(*key_of failures are the instance's own errors (a rewrite-rule collection
  rejecting a non-equation, say); prefix them with this collection's name so the
  user sees the attribute they wrote, not an internal module name.  ONLY `TERM'
  and `THM' are wrapped: anything else -- interrupts in particular -- passes
  through untouched.*)
fun key_of' th = key_of th
  handle TERM (msg, ts) => raise TERM (Binding.name_of name ^ ": " ^ msg, ts)
       | THM (msg, i, ths) => raise THM (Binding.name_of name ^ ": " ^ msg, i, ths);

structure C = iNet_Collection(
  type T = thm
  val eq = Thm.eq_thm_prop
  val key_of = key_of');

val get_net = C.get_net o Context.Proof;
fun content context = map (Thm.transfer'' context) (C.content context);
val get = content o Context.Proof;
val add_thm = C.add o Thm.trim_context;
val del_thm = C.del;
val add = Thm.declaration_attribute add_thm;
val del = Thm.declaration_attribute del_thm;
val setup =
  Attrib.setup name (Attrib.add_del add del) ("declaration of " ^ description) #>
  Global_Theory.add_thms_dynamic (name, content);

end;
