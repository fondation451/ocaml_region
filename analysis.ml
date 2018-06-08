(* No side effect analysis for OCaml with regions *)

open Util

exception Analysis_Error of string

type regions = Check.regions

and pot = Check.pot =
  |PPot of string
  |PLit of int
  |PSize of int
  |PLen of int
  |PNode of int
  |PDepth of int
  |PAdd of pot * pot
  |PMin of pot
  |PMul of pot * pot
  |PUnit

and rgn_pot = Check.rgn_pot

and fun_pot_desc = Check.fun_pot_desc

and integer_prog = pot list

[@@deriving show { with_path = false }]

let mk_pot_with_name name s =
  s := StrSet.add name !s;
  name

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
