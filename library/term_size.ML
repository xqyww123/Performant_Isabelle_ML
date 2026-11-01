(* Smart term size that counts number literals and string literals as small constants.
   - numeral <bits>: size 1
   - uminus (numeral <bits>): size 2
   - Suc (Suc ... 0): size 2
   - String.Literal b0..b6 (Literal ... zero): size 1
   - list of chars (String.char list): size 1 per char + 1 for the list

   Qiyuan Xu (with AI assistance)
*)

local
  fun is_numeral (Const (\<^unchecked_name>\<open>Num.num.One\<close>, _)) = true
    | is_numeral (Const (\<^unchecked_name>\<open>Num.num.Bit0\<close>, _) $ t) = is_numeral t
    | is_numeral (Const (\<^unchecked_name>\<open>Num.num.Bit1\<close>, _) $ t) = is_numeral t
    | is_numeral _ = false

  fun is_nat_literal (Const (\<^unchecked_name>\<open>Groups.zero_class.zero\<close>, _)) = true
    | is_nat_literal (Const (\<^unchecked_name>\<open>Nat.Suc\<close>, _) $ t) = is_nat_literal t
    | is_nat_literal _ = false

  fun is_literal_chain
        (Const (\<^unchecked_name>\<open>Groups.zero_class.zero\<close>,
          Type (\<^unchecked_name>\<open>String.literal\<close>, _))) = true
    | is_literal_chain
        (Const (\<^unchecked_name>\<open>String.Literal\<close>, _) $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ t) =
        is_literal_chain t
    | is_literal_chain _ = false

  fun is_char
        (Const (\<^unchecked_name>\<open>String.char.Char\<close>, _) $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _) = true
    | is_char _ = false

  fun is_char_list
        (Const (\<^unchecked_name>\<open>List.list.Nil\<close>,
          Type (\<^unchecked_name>\<open>List.list\<close>, [Type (\<^unchecked_name>\<open>String.char\<close>, _)]))) =
        true
    | is_char_list (Const (\<^unchecked_name>\<open>List.list.Cons\<close>, _) $ c $ cs) =
        is_char c andalso is_char_list cs
    | is_char_list _ = false

  fun add_size (Const (\<^unchecked_name>\<open>Num.numeral_class.numeral\<close>, _) $ t) n =
        if is_numeral t then n + 1 else add_size t (n + 1)
    | add_size (Const (\<^unchecked_name>\<open>Groups.uminus_class.uminus\<close>, _) $
                  (Const (\<^unchecked_name>\<open>Num.numeral_class.numeral\<close>, _) $ t)) n =
        if is_numeral t then n + 2 else add_size t (n + 2)
    | add_size (t as (Const (\<^unchecked_name>\<open>Nat.Suc\<close>, _) $ _)) n =
        if is_nat_literal t then n + 2 else add_size_default t n
    | add_size
        (t as (Const (\<^unchecked_name>\<open>String.Literal\<close>, _) $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _)) n =
        if is_literal_chain t then n + 1 else add_size_default t n
    | add_size (t as (Const (\<^unchecked_name>\<open>List.list.Cons\<close>, _) $ _ $ _)) n =
        if is_char_list t then n + 1 else add_size_default t n
    | add_size
        (t as (Const (\<^unchecked_name>\<open>List.list.Nil\<close>,
          Type (\<^unchecked_name>\<open>List.list\<close>, [Type (\<^unchecked_name>\<open>String.char\<close>, _)])))) n =
        n + 1
    | add_size t n = add_size_default t n
  and add_size_default (t $ u) n = add_size t (add_size u n)
    | add_size_default (Abs (_, _, t)) n = add_size t (n + 1)
    | add_size_default _ n = n + 1
in
  val smart_size_of_term : term -> int = fn t => add_size t 0
end
