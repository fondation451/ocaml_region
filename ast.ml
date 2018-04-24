(* AST for OCaml with regions *)

type binop =
  |Op_add
  |Op_sub
  |Op_mul
  |Op_div
  |Op_mod
  |Op_and
  |Op_or

and comp =
  |Ceq |Cneq
  |Clt |Cgt
  |Cle |Cge

and self = string

and term =
  |Unit
  |Bool of bool
  |Int of int
  |Var of string
  |Binop of binop * term * term
  |Not of term
  |Neg of term
  |Comp of comp * term * term
  |Fun of self * string list * term * term
  |App of term * term list
  |If of term * term * term
  |Let of string * term * term
  |Letrec of string * term * term
  |Pair of term * term * term
  |Fst of term
  |Snd of term
  |Hd of term
  |Tl of term
  |Nil of term
  |Cons of term * term * term
  |Ref of term * term
  |Assign of term * term
  |Deref of term
  |Newrgn
  |Aliasrgn of term * term
  |Freergn of term
  |Sequence of term * term

[@@deriving show { with_path = false }]
