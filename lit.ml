(* Lit AST *)

open Util

type t =
  | Var of string
  | Lit of int
  | Add of t * t
  | Mul of t * t
  | Div of t * t
[@@deriving show { with_path = false }]

let var v = Var v
let lit i = Lit i
let add l l' = Add (l, l')
let mul l l' = Mul (l, l')
let div l l' = Div (l, l')
let sub l l' = add l (mul (lit (-1)) l')

let fv l =
  let rec loop l out =
    match l with
    | Var v -> StrSet.add v out
    | Add (l1, l2) -> loop l1 (loop l2 out)
    | Mul (l1, l2) -> loop l1 (loop l2 out)
    | Div (l1, l2) -> loop l1 (loop l2 out)
    | _ -> out
  in loop l StrSet.empty

let rec apply s = function
  | Var v -> (try StrMap.find v s with Not_found -> Var v)
  | Add (l1, l2) -> Add (apply s l1, apply s l2)
  | Mul (l1, l2) -> Mul (apply s l1, apply s l2)
  | Div (l1, l2) -> Div (apply s l1, apply s l2)
  | _ as l -> l

let cost_of l =
  let rec loop l out =
    match l with
    | Lit _ -> 0
    | Var _ -> 1
    | Add (l1, l2) | Mul (l1, l2) -> 2 + loop l1 (loop l2 out)
    | Div (l1, l2) -> 10 + loop l1 (loop l2 out)
  in loop l 0
