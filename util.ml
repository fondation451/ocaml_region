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
  "[" ^ (StrMap.fold (fun a v out -> out ^ (Printf.sprintf "%s : %s, \n" a (val_str v))) strmap "") ^ "]"

let list_str l val_str =
  "[" ^ (List.fold_left (fun out v -> out ^ (Printf.sprintf "%s, " (val_str v))) "" l) ^ "]"

let mk_id = let cpt = ref (-1) in fun () -> incr cpt; !cpt

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

let iter_fun f x eq =
  let rec loop x old =
    let e = eq x old in
(*    Printf.printf "E ============== %b\n\n\n" e ;*)
    if e then x else loop (f x) x in
  loop (f x) x

let hash_s s =
  let out = ref 0 in
  for i = 0 to String.length s - 1 do
    out := !out + (Char.code s.[i])
  done;
  !out

let list_min f l =
  match l with
  | [] -> raise (Invalid_argument "Util.list_min: empty list !")
  | h::t ->
    let rec loop l out =
      match l with
      | [] -> out
      | h::t -> if f out h <= 0 then loop t out else loop t h
    in loop t h

type ressource =
  |RPAIR
  |RCONS
  |RNODE
  |RNIL
  |RREF
  |RHND
  |RCLO
[@@deriving show { with_path = false }]

let cost_of ress =
  match ress with
  |RPAIR -> 2
  |RCONS -> 2
  |RNODE -> 2
  |RNIL -> 0
  |RREF -> 1
  |RHND -> 1
  |RCLO -> 1

