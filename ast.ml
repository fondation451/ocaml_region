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

and pot =
  |PPot of string
  |PLit of int
  |PSize of string
  |PLen of string
  |PNode of string
  |PDepth of string
  |PAdd of pot * pot
  |PMin of pot
  |PMul of pot * pot

and rgn_pot = string

and fun_pot_desc = (rgn_pot * (pot * pot)) list

and term =
  |Unit
  |Bool of bool
  |Int of int
  |Var of string
  |Binop of binop * term * term
  |Not of term
  |Neg of term
  |Comp of comp * term * term
  |Fun of self * string list * term * term * fun_pot_desc option
  |App of term * term list
  |If of term * term * term
  |MatchList of term * term * string * string * term
  |MatchTree of term * term * string * string * string * term
  |Let of string * term * term
  |Letrec of string * term * term
  |Pair of term * term * term
  |Fst of term
  |Snd of term
  |Hd of term
  |Tl of term
  |Nil
  |Cons of term * term * term
  |Leaf
  |Node of term * term * term * term
  |Ref of term * term
  |Assign of term * term
  |Deref of term
  |Newrgn
  |Aliasrgn of term * term
  |Freergn of term
  |Sequence of term * term

[@@deriving show { with_path = false }]
