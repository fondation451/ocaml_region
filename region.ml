(* Region for OCaml with regions *)

open Util

exception Region_Error of string

type rcaml_type =
  |TInt
  |TBool
  |TUnit
  |TAlpha of string
  |TFun of rcaml_type list * rcaml_type * regions
  |TCouple of rcaml_type * rcaml_type * regions
  |TList of rcaml_type * regions
  |TRef of rcaml_type * regions
  |THnd of regions
and rcaml_type_poly =
  |TPoly of string list * string list * rcaml_type

and regions = string

and binop = Type.binop =
  |Op_add
  |Op_sub
  |Op_mul
  |Op_div
  |Op_mod
  |Op_and
  |Op_or

and comp = Type.comp =
  |Ceq |Cneq
  |Clt |Cgt
  |Cle |Cge

and self = Type.self

and term =
  |Unit
  |Bool of bool
  |Int of int
  |Var of string
  |Binop of binop * typed_term * typed_term
  |Not of typed_term
  |Neg of typed_term
  |Comp of comp * typed_term * typed_term
  |Fun of self * string list * typed_term * typed_term
  |App of typed_term * typed_term list
  |If of typed_term * typed_term * typed_term
  |Match of typed_term * typed_term * string * string * typed_term
  |Let of string * typed_term * typed_term
  |Letrec of string * typed_term * typed_term
  |Pair of typed_term * typed_term * typed_term
  |Fst of typed_term
  |Snd of typed_term
  |Hd of typed_term
  |Tl of typed_term
  |Nil of typed_term
  |Cons of typed_term * typed_term * typed_term
  |Ref of typed_term * typed_term
  |Assign of typed_term * typed_term
  |Deref of typed_term
  |Newrgn
  |Aliasrgn of typed_term * typed_term
  |Freergn of typed_term
  |Sequence of typed_term * typed_term

and typed_term = {
  rterm : term;
  rtype : rcaml_type_poly;
}

[@@deriving show { with_path = false }]

let mk_term t ty = {rterm = t; rtype = ty}
let get_term t = t.rterm
let get_type t = t.rtype
