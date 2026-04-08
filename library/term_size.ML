(* Smart term size that counts number literals and string literals as small constants.
   - numeral <bits>: size 1
   - uminus (numeral <bits>): size 2
   - Suc (Suc ... 0): size 2
   - String.Literal b0..b6 (Literal ... zero): size 1
   - list of chars (String.char list): size 1 per char + 1 for the list

   Qiyuan Xu (with AI assistance)
*)

local
  fun is_numeral (Const ("Num.num.One", _)) = true
    | is_numeral (Const ("Num.num.Bit0", _) $ t) = is_numeral t
    | is_numeral (Const ("Num.num.Bit1", _) $ t) = is_numeral t
    | is_numeral _ = false

  fun is_nat_literal (Const ("Groups.zero_class.zero", _)) = true
    | is_nat_literal (Const ("Nat.Suc", _) $ t) = is_nat_literal t
    | is_nat_literal _ = false

  fun is_literal_chain (Const ("Groups.zero_class.zero", Type ("String.literal", _))) = true
    | is_literal_chain (Const ("String.Literal", _) $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ t) =
        is_literal_chain t
    | is_literal_chain _ = false

  fun is_char (Const ("String.char.Char", _) $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _) = true
    | is_char _ = false

  fun is_char_list (Const ("List.list.Nil", Type ("List.list", [Type ("String.char", _)]))) = true
    | is_char_list (Const ("List.list.Cons", _) $ c $ cs) = is_char c andalso is_char_list cs
    | is_char_list _ = false

  fun add_size (Const ("Num.numeral_class.numeral", _) $ t) n =
        if is_numeral t then n + 1 else add_size t (n + 1)
    | add_size (Const ("Groups.uminus_class.uminus", _) $
                  (Const ("Num.numeral_class.numeral", _) $ t)) n =
        if is_numeral t then n + 2 else add_size t (n + 2)
    | add_size (t as (Const ("Nat.Suc", _) $ _)) n =
        if is_nat_literal t then n + 2 else add_size_default t n
    | add_size (t as (Const ("String.Literal", _) $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _)) n =
        if is_literal_chain t then n + 1 else add_size_default t n
    | add_size (t as (Const ("List.list.Cons", _) $ _ $ _)) n =
        if is_char_list t then n + 1 else add_size_default t n
    | add_size (t as (Const ("List.list.Nil", Type ("List.list", [Type ("String.char", _)])))) n =
        n + 1
    | add_size t n = add_size_default t n
  and add_size_default (t $ u) n = add_size t (add_size u n)
    | add_size_default (Abs (_, _, t)) n = add_size t (n + 1)
    | add_size_default _ n = n + 1
in
  val smart_size_of_term : term -> int = fn t => add_size t 0
end
