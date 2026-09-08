(*  Title:  library/dynamic_array.ML
    Author: Qiyuan Xu (with AI assistance)

Mutable growable arrays: a length, and an Array.array of at least that
length whose live prefix holds the elements.  Push is amortised O(1),
indexed access costs one comparison more than Array.sub (the index is
checked against the length, not the storage), and every element is stored
directly -- no option box per slot.

Storage.  A polymorphic array can only be allocated with a filler of the
element type, so a dynamic array allocates only while an element is at
hand: a fresh one holds no storage until the first push or insert, whose
element fills the new slots.  Storage doubles on demand and is never given
back by the array itself -- shrinking the length (pop, delete, truncate,
clear) keeps it, so a drained array refills without allocating -- only
shrink_to_fit releases it.  A slot past the length holds the element that
was pushed or inserted when the storage was allocated, or the element at
index 0, written there when the slot was released; hence such a slot may
keep one former element reachable until it is reused or the storage is
released, and the array puts nothing else there.  The hint is the size to
allocate while there is no storage: set by empty, raised by reserve, used
at the next allocation.

A dynamic array is mutable and NOT thread-safe, like the hash tables; and a
traversal (or the ord of sort) must not change the array it is running over
-- it walks the storage and the length that were live when it started, and
a slot released meanwhile reads back as the element at index 0.  An
operation that mutates in place (sort, insert, delete, truncate, pop) is
not exception-safe: if ord raises, or an asynchronous Interrupt arrives in
the middle, the elements are left in an arbitrary state (the length and the
storage invariants still hold).

Copying: Array.copy is a native block move, while ArraySlice.copy is an
element-wise ML loop (polyml basis/Array.sml); a whole array is therefore
moved by Array.copy and only a proper prefix goes through ArraySlice.vector
and Array.copyVec, two native moves.  A shift inside one array overlaps
its own source, so insert and delete stay with ArraySlice.copy, the one
Basis copy that picks the direction; a native move would have to build a
vector of the moved range first.  The traversals delegate to the ArraySlice
loops, which hoist the length and skip the per-element check.
*)

signature DYNAMIC_ARRAY = sig
  type 'a T

  (* construction *)
  val empty       : int -> 'a T                (* capacity hint, allocated at the first push or insert *)
  val make        : 'a list -> 'a T
  val of_array    : 'a array -> 'a T           (* copies *)
  val copy        : 'a T -> 'a T

  (* size *)
  val length      : 'a T -> int
  val is_empty    : 'a T -> bool
  val capacity    : 'a T -> int                (* storage held now *)
  val reserve     : 'a T * int -> unit         (* the storage at the next allocation, or now, is >= n *)
  val shrink_to_fit : 'a T -> unit             (* storage down to the length; none when empty *)

  (* indexed access, Basis spelling; checked against length, raise Subscript *)
  val sub         : 'a T * int -> 'a
  val update      : 'a T * int * 'a -> unit
  (* unchecked against length (Poly/ML still checks against the storage) *)
  val unsafe_sub    : 'a T * int -> 'a
  val unsafe_update : 'a T * int * 'a -> unit

  (* stack end *)
  val push        : 'a T * 'a -> unit          (* amortised O(1) *)
  val push_list   : 'a T * 'a list -> unit
  val pop         : 'a T -> 'a                 (* raises Empty *)
  val last        : 'a T -> 'a                 (* raises Empty *)
  val truncate    : 'a T * int -> unit         (* keep the first n; raises Subscript *)
  val clear       : 'a T -> unit

  (* middle, O(n) shifting; raise Subscript *)
  val insert      : 'a T * int * 'a -> unit    (* i = length is allowed, same as push *)
  val delete      : 'a T * int -> 'a           (* returns the removed element *)

  (* order; ord follows the Isabelle convention (int_ord, string_ord, ...);
     the searches assume the array is sorted by the same ord *)
  val sort          : ('a * 'a -> order) -> 'a T -> unit     (* in place, stable; through one buffer of n slots *)
  val lower_bound   : ('a * 'a -> order) -> 'a T -> 'a -> int   (* first index not LESS than x *)
  val upper_bound   : ('a * 'a -> order) -> 'a T -> 'a -> int   (* first index GREATER than x *)
  val binary_search : ('a * 'a -> order) -> 'a T -> 'a -> int option  (* first index EQUAL to x *)
  val insert_sorted : ('a * 'a -> order) -> 'a T -> 'a -> unit  (* after the elements EQUAL to x: keeps insertion order, like sort *)

  (* traversal, Pure Array naming *)
  val fold        : ('a -> 'b -> 'b) -> 'a T -> 'b -> 'b
  val fold_rev    : ('a -> 'b -> 'b) -> 'a T -> 'b -> 'b
  val fold_index  : (int * 'a -> 'b -> 'b) -> 'a T -> 'b -> 'b
  val app         : ('a -> unit) -> 'a T -> unit
  val exists      : ('a -> bool) -> 'a T -> bool
  val forall      : ('a -> bool) -> 'a T -> bool
  val get_first   : ('a -> 'b option) -> 'a T -> 'b option
  val member      : ('a * 'a -> bool) -> 'a T -> 'a -> bool
  val map         : ('a -> 'b) -> 'a T -> 'b T

  (* conversion, copying the live prefix only *)
  val dest        : 'a T -> 'a list
  val to_array    : 'a T -> 'a array
  val to_vector   : 'a T -> 'a vector
end

structure Dynamic_Array: DYNAMIC_ARRAY = struct

datatype 'a T = Dynamic_Array of {
  hint: int Unsynchronized.ref,       (*size of the next allocation, while there is no storage*)
  len: int Unsynchronized.ref,
  arr: 'a array Unsynchronized.ref}   (*len <= Array.length; a filler is at index 0 unless the storage is empty*)

val min_capacity = 16   (*floor for the hint: the smallest storage allocated from nothing;
                          storage sized to fit (make, of_array, copy, shrink_to_fit) doubles from its size*)
val insertion_threshold = 8   (*sort: ranges up to this size by insertion*)



(** storage **)

fun no_storage () = Array.fromList []

(*the first n elements of src (n <= length src)*)
fun prefix_slice src n = ArraySlice.slice (src, 0, SOME n)
fun prefix_vector src n = ArraySlice.vector (prefix_slice src n)

(*move the first n elements of src to dst at 0: a whole array by one native
  Array.copy, a proper prefix through a vector (ArraySlice.copy is an ML loop)*)
fun move_prefix src n dst =
  if n = Array.length src then Array.copy {src = src, dst = dst, di = 0}
  else Array.copyVec {src = prefix_vector src n, dst = dst, di = 0}

fun prefix_array src n =
  if n = 0 then no_storage ()
  else let val dst = Array.array (n, Array.sub (src, 0)) in move_prefix src n dst; dst end

fun make_from hint n arr =
  Dynamic_Array {hint = Unsynchronized.ref hint, len = Unsynchronized.ref n, arr = Unsynchronized.ref arr}

fun empty hint = make_from (Int.max (hint, min_capacity)) 0 (no_storage ())

fun length (Dynamic_Array {len, ...}) = !len
fun is_empty d = length d = 0
fun capacity (Dynamic_Array {arr, ...}) = Array.length (!arr)

(*storage of at least n slots, x filling the fresh ones; only called with n > capacity*)
fun grow (Dynamic_Array {hint, len, arr}) n x =
  let
    val a = !arr
    val cap = Array.length a
    (*n itself is never capped, only the size chosen for it: Poly/ML refuses length >= maxLen (basis/Array.sml:70)*)
    val cap' = Int.max (n, Int.min (Array.maxLen - 1, if cap = 0 then !hint else 2 * cap))
    val a' = Array.array (cap', x)   (*n >= Array.maxLen raises Size here*)
  in move_prefix a (!len) a'; arr := a' end

(*the storage, with room for n elements; x fills any fresh slots*)
fun room (d as Dynamic_Array {arr, ...}) n x =
  let val a = !arr in if n <= Array.length a then a else (grow d n x; !arr) end

(*the length becomes n <= length: the released slots are overwritten by the
  element at index 0 so that they keep nothing else reachable*)
fun release (Dynamic_Array {len, arr, ...}) n =
  let
    val a = !arr
    val n0 = !len
    fun overwrite x0 i = if i < n0 then (Array.update (a, i, x0); overwrite x0 (i + 1)) else ()
  in
    if n < n0 then overwrite (Array.sub (a, 0)) n else ();
    len := n
  end

fun reserve (d as Dynamic_Array {hint, arr, ...}, n) =
  let val a = !arr in
    if n <= Array.length a then ()
    else if Array.length a = 0 then hint := Int.max (!hint, n)   (*no filler yet*)
    else grow d n (Array.sub (a, 0))
  end

fun shrink_to_fit (Dynamic_Array {len, arr, ...}) =
  if !len < Array.length (!arr) then arr := prefix_array (!arr) (!len) else ()



(** indexed access **)

fun sub (Dynamic_Array {len, arr, ...}, i) =
  if i < !len then Array.sub (!arr, i) else raise Subscript   (*i < 0 fails in Array.sub*)

fun update (Dynamic_Array {len, arr, ...}, i, x) =
  if i < !len then Array.update (!arr, i, x) else raise Subscript

fun unsafe_sub (Dynamic_Array {arr, ...}, i) = Array.sub (!arr, i)
fun unsafe_update (Dynamic_Array {arr, ...}, i, x) = Array.update (!arr, i, x)



(** stack end **)

fun push (d as Dynamic_Array {len, ...}, x) =
  let
    val n = !len
    val a = room d (n + 1) x
  in Array.update (a, n, x); len := n + 1 end

fun push_list (_, []) = ()
  | push_list (d as Dynamic_Array {len, ...}, xs as x :: _) =
      let
        val n = !len
        val a = room d (n + List.length xs) x
        fun fill i [] = len := i
          | fill i (y :: ys) = (Array.update (a, i, y); fill (i + 1) ys)
      in fill n xs end

fun last (Dynamic_Array {len, arr, ...}) =
  let val n = !len in if n = 0 then raise Empty else Array.sub (!arr, n - 1) end

fun pop d = let val x = last d in release d (length d - 1); x end

fun truncate (d as Dynamic_Array {len, ...}, n) =
  if n < 0 orelse n > !len then raise Subscript else release d n

fun clear d = release d 0



(** middle **)

fun insert (d as Dynamic_Array {len, ...}, i, x) =
  let val n = !len in
    if i < 0 orelse i > n then raise Subscript
    else
      let val a = room d (n + 1) x in
        ArraySlice.copy {src = ArraySlice.slice (a, i, SOME (n - i)), dst = a, di = i + 1};
        Array.update (a, i, x);
        len := n + 1
      end
  end

fun delete (d as Dynamic_Array {len, arr, ...}, i) =
  let
    val n = !len
    val _ = if i < 0 orelse i >= n then raise Subscript else ()
    val a = !arr
    val x = Array.sub (a, i)
  in
    ArraySlice.copy {src = ArraySlice.slice (a, i + 1, SOME (n - i - 1)), dst = a, di = i};
    release d (n - 1);
    x
  end



(** order **)

(*stable merge sort between the storage and one buffer, the two swapping
  roles per level: msort src dst sorts [lo, hi) into dst, merging the two
  sorted halves from src; a leaf instead reads its elements from the storage,
  which still holds that range untouched because every call writes only
  inside its own range and a merge runs after both its children.  Small
  ranges by insertion.*)
fun sort ord (Dynamic_Array {len, arr, ...}) =
  let
    val n = !len
    val a = !arr
    (*below the threshold there is no buffer: the top call is then one insertion
      sort, which reads a[i] before shifting and so tolerates dst = a -- and n = 0,
      where there is no element to fill a buffer with*)
    val b = if n <= insertion_threshold then a else Array.array (n, Array.sub (a, 0))

    fun insertion_sort dst lo hi =
      let
        fun sink i x =
          if i > lo andalso ord (Array.sub (dst, i - 1), x) = GREATER
          then (Array.update (dst, i, Array.sub (dst, i - 1)); sink (i - 1) x)
          else Array.update (dst, i, x)
        fun loop i = if i < hi then (sink i (Array.sub (a, i)); loop (i + 1)) else ()
      in loop lo end

    fun merge src dst lo mid hi =
      let
        fun emit k x = Array.update (dst, k, x)
        fun go i j k =
          if k = hi then ()
          else if j = hi then (emit k (Array.sub (src, i)); go (i + 1) j (k + 1))
          else if i = mid then (emit k (Array.sub (src, j)); go i (j + 1) (k + 1))
          else
            let val x = Array.sub (src, i); val y = Array.sub (src, j) in
              if ord (x, y) = GREATER then (emit k y; go i (j + 1) (k + 1))
              else (emit k x; go (i + 1) j (k + 1))   (*EQUAL: the left one first, stable*)
            end
      in go lo mid lo end

    fun msort src dst lo hi =
      if hi - lo <= insertion_threshold then insertion_sort dst lo hi
      else
        let val mid = (lo + hi) div 2 in
          msort dst src lo mid;
          msort dst src mid hi;
          merge src dst lo mid hi
        end
  in msort b a 0 n end

(*the first index whose element fails test, test holding on a prefix*)
fun bound_search test (Dynamic_Array {len, arr, ...}) =
  let
    val a = !arr
    fun search lo hi =   (*answer in [lo, hi]*)
      if lo = hi then lo
      else
        let val mid = (lo + hi) div 2 in
          if test (Array.sub (a, mid)) then search (mid + 1) hi else search lo mid
        end
  in search 0 (!len) end

fun lower_bound ord d x = bound_search (fn y => ord (y, x) = LESS) d
fun upper_bound ord d x = bound_search (fn y => ord (y, x) <> GREATER) d

fun binary_search ord (d as Dynamic_Array {len, arr, ...}) x =
  let val i = lower_bound ord d x in
    if i < !len andalso ord (Array.sub (!arr, i), x) = EQUAL then SOME i else NONE
  end

fun insert_sorted ord d x = insert (d, upper_bound ord d x, x)



(** traversal **)

(*the live prefix as a slice; it starts at 0, so foldli's index is the array index*)
fun live (Dynamic_Array {len, arr, ...}) = prefix_slice (!arr) (!len)

fun fold f d y = ArraySlice.foldl (fn (x, y) => f x y) y (live d)
fun fold_rev f d y = ArraySlice.foldr (fn (x, y) => f x y) y (live d)
fun fold_index f d y = ArraySlice.foldli (fn (i, x, y) => f (i, x) y) y (live d)
fun app f d = ArraySlice.app f (live d)
fun exists P d = ArraySlice.exists P (live d)
fun forall P d = ArraySlice.all P (live d)
fun member eq d x = exists (fn y => eq (x, y)) d

(*no ArraySlice loop returns the result of f*)
fun get_first f (Dynamic_Array {len, arr, ...}) =
  let
    val a = !arr
    val n = !len
    fun go i =
      if i < n then (case f (Array.sub (a, i)) of NONE => go (i + 1) | some => some) else NONE
  in go 0 end

fun map f (Dynamic_Array {hint, len, arr}) =
  let val a = !arr
  in make_from (!hint) (!len) (Array.tabulate (!len, fn i => f (Array.sub (a, i)))) end



(** conversion **)

fun make xs = let val a = Array.fromList xs in make_from min_capacity (Array.length a) a end

fun of_array a = make_from min_capacity (Array.length a) (prefix_array a (Array.length a))

fun copy (Dynamic_Array {hint, len, arr}) = make_from (!hint) (!len) (prefix_array (!arr) (!len))

fun dest d = fold_rev cons d []

fun to_array (Dynamic_Array {len, arr, ...}) = prefix_array (!arr) (!len)

fun to_vector (Dynamic_Array {len, arr, ...}) = prefix_vector (!arr) (!len)

end
