(* Region checked for OCaml with regions *)

open Util

exception Error of string

type rcaml_type =
  |TInt
  |TBool
  |TUnit
  |TAlpha of string
  |TFun of (string * string) list *
           rcaml_type list * rcaml_type * regions *
           capabilities * capabilities * effects
  |TCouple of rcaml_type * rcaml_type * regions
  |TList of list_sized * rcaml_type * regions
  |TRef of int * rcaml_type * regions
  |THnd of regions

and regions = Simpl.regions

and list_sized = Simpl.list_sized

and capability =
  |Linear
  |Relaxed

and capabilities = (regions * capability) list

and effect =
  |ERead of regions
  |EWrite of regions
  |EAlloc of regions

and effects = effect list

and binop = Simpl.binop =
  |Op_add
  |Op_sub
  |Op_mul
  |Op_div
  |Op_mod
  |Op_and
  |Op_or

and comp = Simpl.comp =
  |Ceq |Cneq
  |Clt |Cgt
  |Cle |Cge

and self = Simpl.self

and pot = Simpl.pot =
  |PPot of string
  |PLit of int
  |PSize of int
  |PLen of int
  |PAdd of pot * pot
  |PMin of pot
  |PMul of pot * pot
  |PUnit

and rgn_pot = Simpl.rgn_pot

and fun_pot_desc = Simpl.fun_pot_desc

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

let empty_gamma = []
let empty_capabilities = []
let empty_effects = []

let effects_of l = l
let cap_of l = List.map (fun r -> (r, Relaxed)) l
let cap_of_strmap s = StrMap.bindings s

let add_cap r p c = (r, p)::(List.remove_assoc r c)
let remove_cap r c = List.remove_assoc r c
let diff_cap c1 c2 = List.fold_left (fun out (r, p) -> List.remove_assoc r out) c1 c2
let union_cap c1 c2 = List.fold_left (fun out (r, p) -> add_cap r p out) c2 c1

let cap_map f c =
  List.fold_left
    (fun out (r, p) ->
      let r', p' = f (r, p) in
      add_cap r' p' out)
    empty_capabilities
    c
let cap_forall f c = List.for_all f c

let merge_effects e1 e2 = List.rev_append e1 (List.fold_left (fun out x -> List.filter (fun y -> x <> y) out) e2 e1)
let add_effects e phi = e::(List.filter (fun e' -> e' <> e) phi)
let effects_map f phi =
  List.fold_left
    (fun out e -> add_effects (f e) out)
    empty_effects
    phi (* Bug ordre d'insertion, effacement TODO *)

let cap r c = List.mem_assoc r c
let cap_find r c = List.assoc r c
let cap_linear r c = try List.assoc r c = Linear with Not_found -> false
let cap_relaxed r c = try List.assoc r c = Relaxed with Not_found -> false

let gamma_remove r g = List.filter (fun r' -> r' <> r) g
let gamma_add r g = r::(gamma_remove r g)
let gamma_mem r g = List.mem r g
