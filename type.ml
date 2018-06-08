(* Type for OCaml with regions *)

open Util

exception Error of string

type rcaml_type =
  |TInt
  |TBool
  |TUnit
  |TAlpha of string
  |TFun of rcaml_type list * rcaml_type * regions
  |TCouple of rcaml_type * rcaml_type * regions
  |TList of list_sized * rcaml_type * regions
  |TTree of  list_sized * list_sized * rcaml_type * regions
  |TRef of int * rcaml_type * regions
  |THnd of regions
and rcaml_type_poly =
  |TPoly of string list * string list * rcaml_type

and regions =
  |RRgn of string
  |RAlpha of string

and list_sized = int option

and binop = Ast.binop =
  |Op_add
  |Op_sub
  |Op_mul
  |Op_div
  |Op_mod
  |Op_and
  |Op_or

and comp = Ast.comp =
  |Ceq |Cneq
  |Clt |Cgt
  |Cle |Cge

and self = Ast.self

and pot = Ast.pot =
  |PPot of string
  |PLit of int
  |PSize of string
  |PLen of string
  |PAdd of pot * pot
  |PMin of pot
  |PMul of pot * pot

and rgn_pot = Ast.rgn_pot

and fun_pot_desc = Ast.fun_pot_desc

and term =
  |Unit
  |Bool of bool
  |Int of int
  |Var of string
  |Binop of binop * typed_term * typed_term
  |Not of typed_term
  |Neg of typed_term
  |Comp of comp * typed_term * typed_term
  |Fun of self * string list * typed_term * typed_term * fun_pot_desc option
  |App of typed_term * typed_term list
  |If of typed_term * typed_term * typed_term
  |MatchList of typed_term * typed_term * string * string * typed_term
  |MatchTree of typed_term * typed_term * string * string * string * typed_term
  |Let of string * typed_term * typed_term
  |Letrec of string * typed_term * typed_term
  |Pair of typed_term * typed_term * typed_term
  |Fst of typed_term
  |Snd of typed_term
  |Hd of typed_term
  |Tl of typed_term
  |Nil
  |Cons of typed_term * typed_term * typed_term
  |Leaf
  |Node of typed_term * typed_term * typed_term * typed_term
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
