(*
  Generic Mutable Hash Table Functor

  Open-addressing with linear probing, generalized from PolyML's HashArray.ML.
  Power-of-two capacity with bitmask indexing for fast modular arithmetic.

  Design:
    - Mutable imperative API (update/delete return unit)
    - Tracks tombstones separately; rehashes when (used + deleted) exceeds 75% load
    - On insert, records first tombstone seen during probe for reuse
    - Rehash targets ~25% load (new capacity = next_pow2(used * 4), minimum 16)
*)

signature HASH_KEY = sig
  type key
  val hash: key -> word
  val eq: key * key -> bool
end

signature HASH_TABLE = sig
  structure Key: HASH_KEY
  type key
  type 'a table
  exception DUP of key
  exception UNDEF of key

  val empty: int -> 'a table
  val size: 'a table -> int
  val is_empty: 'a table -> bool
  val lookup: 'a table -> key -> 'a option
  val defined: 'a table -> key -> bool
  val update: 'a table -> key * 'a -> unit
  val update_new: 'a table -> key * 'a -> unit
  val delete: 'a table -> key -> unit
  val delete_safe: 'a table -> key -> unit
  val fold: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val dest: 'a table -> (key * 'a) list
  val keys: 'a table -> key list
  val exists: (key * 'a -> bool) -> 'a table -> bool
  val forall: (key * 'a -> bool) -> 'a table -> bool
  val map: (key -> 'a -> 'b) -> 'a table -> 'b table
  val make: (key * 'a) list -> 'a table
end

functor Hash_Table(Key: HASH_KEY): HASH_TABLE = struct

structure Key = Key
type key = Key.key

exception DUP of key
exception UNDEF of key

datatype 'a entry = Empty | Deleted | Used of key * 'a

datatype 'a table = Table of {
  used: int Unsynchronized.ref,
  deleted: int Unsynchronized.ref,
  entries: 'a entry array Unsynchronized.ref
}

fun next_pow2 n =
  let
    fun go p = if p >= n then p else go (p * 2)
  in go 1 end

fun new_capacity used =
  let val c = next_pow2 (Int.max (used * 4, 16))
  in c end

fun empty hint =
  let val cap = next_pow2 (Int.max (hint, 16))
  in Table {
    used = Unsynchronized.ref 0,
    deleted = Unsynchronized.ref 0,
    entries = Unsynchronized.ref (Array.array (cap, Empty))
  } end

fun size (Table {used, ...}) = !used

fun is_empty tab = size tab = 0

fun index h cap = Word.toInt (Word.andb (h, Word.fromInt (cap - 1)))

fun lookup (Table {entries, ...}) k =
  let
    val arr = !entries
    val cap = Array.length arr
    val start = index (Key.hash k) cap
    fun find i =
      case Array.sub (arr, i) of
        Empty => NONE
      | Deleted => find (if i + 1 = cap then 0 else i + 1)
      | Used (k', v) =>
          if Key.eq (k, k') then SOME v
          else find (if i + 1 = cap then 0 else i + 1)
  in find start end

fun defined tab k = is_some (lookup tab k)

fun rehash (Table {used, deleted, entries}) =
  let
    val old_arr = !entries
    val n = !used
    val cap = new_capacity n
    val arr = Array.array (cap, Empty)
    fun insert_entry (Used (k, v)) =
          let
            val start = index (Key.hash k) cap
            fun find i =
              case Array.sub (arr, i) of
                Empty => Array.update (arr, i, Used (k, v))
              | _ => find (if i + 1 = cap then 0 else i + 1)
          in find start end
      | insert_entry _ = ()
  in
    Array.app insert_entry old_arr;
    deleted := 0;
    entries := arr
  end

fun maybe_rehash (tab as Table {used, deleted, entries, ...}) =
  let val cap = Array.length (!entries)
  in if (!used + !deleted) * 4 > cap * 3 then rehash tab else () end

fun update (tab as Table {used, deleted, entries, ...}) (k, v) =
  let
    val arr = !entries
    val cap = Array.length arr
    val start = index (Key.hash k) cap
    (* Probe for key, tracking first tombstone *)
    fun find i tomb =
      case Array.sub (arr, i) of
        Empty =>
          (* Key not found; insert at tombstone if available, else here *)
          let val j = case tomb of SOME t => t | NONE => i
          in
            Array.update (arr, j, Used (k, v));
            (case tomb of
              SOME _ => deleted := !deleted - 1
            | NONE => ());
            used := !used + 1
          end
      | Deleted =>
          let val tomb' = case tomb of NONE => SOME i | _ => tomb
          in find (if i + 1 = cap then 0 else i + 1) tomb' end
      | Used (k', _) =>
          if Key.eq (k, k') then Array.update (arr, i, Used (k, v))
          else find (if i + 1 = cap then 0 else i + 1) tomb
  in
    find start NONE;
    maybe_rehash tab
  end

fun update_new (tab as Table {entries, ...}) (k, v) =
  let
    val arr = !entries
    val cap = Array.length arr
    val start = index (Key.hash k) cap
    fun check i =
      case Array.sub (arr, i) of
        Empty => ()
      | Deleted => check (if i + 1 = cap then 0 else i + 1)
      | Used (k', _) =>
          if Key.eq (k, k') then raise DUP k
          else check (if i + 1 = cap then 0 else i + 1)
  in
    check start;
    update tab (k, v)
  end

fun delete (Table {used, deleted, entries, ...}) k =
  let
    val arr = !entries
    val cap = Array.length arr
    val start = index (Key.hash k) cap
    fun find i =
      case Array.sub (arr, i) of
        Empty => raise UNDEF k
      | Deleted => find (if i + 1 = cap then 0 else i + 1)
      | Used (k', _) =>
          if Key.eq (k, k') then
            (Array.update (arr, i, Deleted);
             used := !used - 1;
             deleted := !deleted + 1)
          else find (if i + 1 = cap then 0 else i + 1)
  in find start end

fun delete_safe tab k = delete tab k handle UNDEF _ => ()

fun fold f (Table {entries, ...}) init =
  Array.foldl
    (fn (Used (k, v), acc) => f (k, v) acc | (_, acc) => acc)
    init (!entries)

fun dest tab = fold (fn (k, v) => fn acc => (k, v) :: acc) tab []

fun keys tab = fold (fn (k, _) => fn acc => k :: acc) tab []

fun exists pred (Table {entries, ...}) =
  let
    val arr = !entries
    val cap = Array.length arr
    fun check i =
      if i >= cap then false
      else case Array.sub (arr, i) of
        Used (k, v) => pred (k, v) orelse check (i + 1)
      | _ => check (i + 1)
  in check 0 end

fun forall pred tab = not (exists (fn kv => not (pred kv)) tab)

fun map f tab =
  let
    val n = size tab
    val tab' = empty n
  in
    fold (fn (k, v) => fn () => update tab' (k, f k v)) tab ();
    tab'
  end

fun make pairs =
  let
    val tab = empty (length pairs)
  in
    List.app (fn (k, v) => update tab (k, v)) pairs;
    tab
  end

end

(* Integer hash: Knuth multiplicative hash *)
val hash_int_multiplier : word = 0w2654435761

fun hash_int (k: int) : word = Word.* (Word.fromInt k, hash_int_multiplier)

structure Inthashtab = Hash_Table(
  type key = int
  val eq = (op =) : int * int -> bool
  val hash = hash_int
)

(* String hash: FNV-1a folded to native word *)
fun hash_string (s: string) : word =
  let
    val bytes = Byte.stringToBytes s
    val len = Word8Vector.length bytes
    val h = Unsynchronized.ref (0wxCBF29CE484222325 : Word64.word)
    val prime = 0wx100000001B3 : Word64.word
    val i = Unsynchronized.ref 0
  in
    while !i < len do
      (h := Word64.* (Word64.xorb (!h, Word64.fromLargeWord (Word8.toLargeWord (Word8Vector.sub (bytes, !i)))), prime);
       i := !i + 1);
    Word.fromLargeWord (Word64.toLargeWord (!h))
  end

structure Strhashtab = Hash_Table(
  type key = string
  val eq = (op =) : string * string -> bool
  val hash = hash_string
)
