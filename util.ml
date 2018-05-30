(* UTIL for OCaml with regions *)

module StrSet = Set.Make(struct
  type t = string
  let compare = String.compare
end)

module StrMap = Map.Make(struct
  type t = string
  let compare = String.compare
end)

let strset_str strset =
  "[" ^ (StrSet.fold (fun a out -> out ^ (Printf.sprintf "%s, " a)) strset "") ^ "]"

let strmap_str strmap val_str =
  "[" ^ (StrMap.fold (fun a v out -> out ^ (Printf.sprintf "%s : %s, " a (val_str v))) strmap "") ^ "]"

let mk_var =
  let alpha = [|"a" ; "b" ; "c" ; "d" ; "e" ; "f" ; "g" ; "h" ; "i" ; "j" ; "k" ; "l" ; "m" ;
                "n" ; "o" ; "p" ; "q" ; "r" ; "s" ; "t" ; "u" ; "v" ; "w" ; "x" ; "y" ; "z" |] in
  let cpt = ref (-1) in
  fun () -> incr cpt; (alpha.(!cpt mod 26))^(string_of_int (!cpt / 26))

let mk_rgn = let cpt = ref (-1) in fun () -> incr cpt;
  let out = "rgn"^(string_of_int !cpt) in
  (* Printf.printf "###################### CREATION %s ###################" out; *)
  out

let strmap_diff m1 m2 = StrMap.filter (fun k v -> StrMap.mem k m2) m1

type ressource =
  |RPAIR
  |RCONS
  |RNIL
  |RREF
  |RHND
  |RCLO
[@@deriving show { with_path = false }]

let cost_of ress =
  match ress with
  |RPAIR -> 2
  |RCONS -> 2
  |RNIL -> 0
  |RREF -> 1
  |RHND -> 1
  |RCLO -> 1
