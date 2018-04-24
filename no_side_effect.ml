(* No side effect analysis for OCaml with regions *)

open Util

exception No_Side_Effect_Error of string

type potential = string

and integer_prog_expr = potential * int

and integer_prog_line = integer_prog_expr list * int

and integer_prog = integer_prog_line list

and ressource =
  |RPAIR
  |RCONS
  |RNIL
  |RREF
  |RHND

[@@deriving show { with_path = false }]

let cpt = ref (-1)
let mk_pot s =
  incr cpt;
  let out = "pot"^(string_of_int !cpt) in
  s := StrSet.add out !s;
  out

let mk_pot' str s =
  incr cpt;
  let out = str^(string_of_int !cpt) in
  s := StrSet.add out !s;
  out

let cost_of ress =
  match ress with
  |RPAIR -> 2
  |RCONS -> 2
  |RNIL -> 0
  |RREF -> 1
  |RHND -> 1
