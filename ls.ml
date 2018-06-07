(* Type for OCaml with regions *)

open Util

exception Error of string

type rcaml_type = Type.rcaml_type =
  |TInt
  |TBool
  |TUnit
  |TAlpha of string
  |TFun of rcaml_type list * rcaml_type * regions
  |TCouple of rcaml_type * rcaml_type * regions
  |TList of list_sized * rcaml_type * regions
  |TRef of int * rcaml_type * regions
  |THnd of regions

and regions = Type.regions =
  |RRgn of string
  |RAlpha of string

and list_sized = Type.list_sized

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

and pot = Type.pot =
  |PPot of string
  |PLit of int
  |PSize of string
  |PLen of string
  |PAdd of pot * pot
  |PMin of pot
  |PMul of pot * pot

and rgn_pot = Type.rgn_pot

and fun_pot_desc = Type.fun_pot_desc

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
  |Let of string * typed_term * typed_term
  |Letrec of string * typed_term * typed_term
  |Pair of typed_term * typed_term * typed_term
  |Fst of typed_term
  |Snd of typed_term
  |Hd of typed_term
  |Tl of typed_term
  |Nil
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
  rtype : rcaml_type;
  ralpha_l : string list;
  rrgn_l : string list;
}

[@@deriving show { with_path = false }]

let mk_term t mty alpha_l rgn_l = {
  rterm = t;
  rtype = mty;
  ralpha_l = alpha_l;
  rrgn_l = rgn_l;
}
let get_term t = t.rterm
let get_type t = t.rtype
let get_alpha_l t = t.ralpha_l
let get_rgn_l t = t.rrgn_l
