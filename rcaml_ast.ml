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

and term =
  |TUnit
  |TBool of bool
  |TInt of int
  |TVar of string
  |TBinop of binop * term * term
  |TNot of term
  |TNeg of term
  |TComp of comp * term * term
  |TFun of string * term * term
  |TApp of term * term
  |TIf of term * term * term
  |TLet of string * term * term
  |TLetrec of string * string * term * term * term
  |TPair of term * term * term
  |TFst of term
  |TSnd of term
  |TNil of term
  |TCons of term * term * term
  |TRef of term * term
  |TAssign of term * term
  |TDeref of term
  |TNewrgn
  |TAliasrgn of term * term
  |TFreergn of term

[@@deriving show { with_path = false }]
