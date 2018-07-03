(* Litteral Expressions Management *)

open Util

exception Bad_equation

type t =
  | Var of string
  | Lit of int
  | Add of t list
  | Mul of t list
  | Unit
[@@deriving show { with_path = false }]

let remove_from_list l f =
  let rec loop l out =
    match l with
    | [] -> None
    | h::t ->
      if f h then
        Some (List.rev_append t out)
      else
        loop t (h::out)
  in loop l []

let rec equal l l' =
  match l, l' with
  | Var v, Var v' -> v = v'
  | Lit i, Lit i' -> i = i'
  | Add l_l, Add l_l' | Mul l_l, Mul l_l' ->
    let rec loop l_l l_l' =
      match l_l with
      | [] -> l_l' = []
      | h::t -> begin
        match remove_from_list l_l' (equal h) with
        | None -> false
        | Some t' -> loop t t'
      end
    in loop l_l l_l'
  | Unit, Unit -> true
  | _ -> false

let rec compare_l l_l l_l' out =
  match l_l, l_l' with
  | [], [] -> out
  | [], rem -> out - List.length rem
  | rem, [] -> out + List.length rem
  | h::t, h'::t' -> compare_l t t' (out + compare h h')
and compare l l' =
  match l, l' with
  | Var v, Var v' ->
    let h = hash_s v and h'= hash_s v' in
    if h > h' then 1 else if h < h' then -1 else 0
  | Lit i, Lit i' -> Pervasives.compare i i'
  | Add l_l, Add l_l' | Mul l_l, Mul l_l' -> compare_l l_l l_l' 0
  | Unit, Unit -> 0
  | Mul _, _ -> 1
  | Add _, Mul _ -> -1
  | Add _, Var _ | Add _, Lit _ -> 1
  | Var _, Mul _ | Var _, Add _ -> -1
  | Var _, Lit _ -> 1
  | Lit _, _ -> -1
  | _ -> 0

let fv lit =
  let rec loop lit out =
    match lit with
    | Var v -> StrSet.add v out
    | Add l_l | Mul l_l -> List.fold_left (fun out l -> loop l out) out l_l
    | _ -> out
  in loop lit StrSet.empty

let rec order = function
  | Add p_l -> Add (List.sort compare p_l)
  | Mul p_l -> Mul (List.sort compare p_l)
  | _ as unchanged -> unchanged

let simplify lit =
  let rec loop = function
    | Add [] -> Lit 0
    | Mul [] -> Lit 1
    | Add l | Mul l when List.tl l = [] -> List.hd l
    | Add l_l -> Add (List.filter (fun l -> l <> Unit && l <> Lit 0) (List.map loop l_l))
    | Mul l_l ->
      if List.mem (Lit 0) l_l then
        Lit 0
      else
        Mul (List.filter (fun l -> l <> Unit) (List.map loop l_l))
    | _ as unchanged -> unchanged
  in
  let out = iter_fun loop lit equal in
(*  Printf.printf "simplify %s\n" (show out);*)
  order out

let separate l_l =
  let rec loop l_l out_i out_l =
    match l_l with
    | l::l_l' -> begin
      match l with
      | Lit i -> loop l_l' (i::out_i) out_l
      | _ -> loop l_l' out_i (l::out_l)
    end
    | [] -> out_i, out_l
  in loop l_l [] []

let agg lit =
  let rec loop = function
    | Add l_l ->
      let l_l' =
        List.fold_left
          (fun out l ->
            match loop l with
            | Add l_l' -> List.rev_append l_l' out
            | _ as l'-> l'::out)
          [] l_l
      in
      let i_l, l_l = separate l_l' in
      let i = List.fold_left (fun out i -> out + i) 0 i_l in
      if i = 0 then
        Add l_l
      else
        Add ((Lit i)::l_l)
    | Mul l_l ->
      let l_l' =
        List.fold_left
          (fun out l ->
            match loop l with
            | Mul l_l' -> List.rev_append l_l' out
            | _ as l' -> l'::out)
          [] l_l
      in
      let i_l, l_l = separate l_l' in
      let i = List.fold_left (fun out i -> out * i) 1 i_l in
      if i = 1 then
        Mul l_l
      else
        Mul ((Lit i)::l_l)
    | _ as out -> out
  in
  let out = loop lit in
(*  Printf.printf "agg loop %s\n" (show out);*)
  simplify out

let rec exp l_l out =
  match l_l with
  | [] -> out
  | [l] -> l::out
  | l::(l'::t as l_l') -> begin
    match l, l' with
    | f, Add add_l | Add add_l, f -> (Add (List.map (fun lit -> Mul [lit ; f]) add_l))::t
    | _ -> exp l_l' (l::out)
  end

let expansion lit =
  let rec loop = function
    | Mul l_l as unchanged ->
      let l_l = List.map loop l_l in
      Mul (exp l_l [])
    | Add l_l -> Add (List.map loop l_l)
    | _ as unchanged -> unchanged
  in
  let out = loop lit in
  Printf.printf "expansion loop %s\n" (show out);
  agg out

let fact l l' =
  match l, l' with
  | Var v, Var v' when v = v' -> l, Lit 2
  | Var v, Mul l_l | Mul l_l, Var v ->
    if List.mem (Var v) l_l then
      l, Add ((Lit 1)::(List.filter (fun l -> l <> Var v) l_l))
    else
      Unit, Unit
  | Mul l_l, Mul l_l' -> begin
    let pot_l = List.filter (function |Var _ -> true | _ -> false) l_l in
    let pot_l' = List.filter (function |Var _ -> true | _ -> false) l_l' in
    match List.filter (fun l -> List.mem l pot_l') pot_l with
    |[] -> Unit, Unit
    |l_com::_ ->
      let not_l_com l = l <> l_com in
      l_com, Add [Mul (List.filter (fun l -> l <> l_com) l_l) ; Mul (List.filter (fun l -> l <> l_com) l_l')]
  end
  | _ -> Unit, Unit

let factorize lit =
  let rec factorize_loop = function
    | Add l_l ->
      let l_l = List.map factorize_loop l_l in
      let rec loop_l l l_l out =
        match l_l with
        | [] -> None
        | l'::l_l' -> begin
          match fact l l' with
          | Unit, Unit -> loop_l l l_l' (l'::out)
          | f, add_l -> Some (List.rev_append l_l' ((Mul [f ; add_l])::out))
        end
      in
      let rec loop l_l out =
        match l_l with
        | [] -> out
        | l::l_l' -> begin
          match loop_l l l_l' [] with
          | None -> loop l_l' (l::out)
          | Some l_l'' -> List.rev_append out l_l''
        end
      in
      Add (loop l_l [])
    | Mul l_l -> Mul (List.map factorize_loop l_l)
    | _ as unchanged -> unchanged
  in
  iter_fun
    (fun lit ->
      let out = factorize_loop lit in
(*      Printf.printf "factorize loop %s\n" (show out);*)
      let out = agg out in
(*      Printf.printf "OUT FACTORISE %s\n" (show out);*) out) lit equal

let rec uapply env = function
  | Var var when StrMap.mem var env -> StrMap.find var env
  | Add l_l -> Add (List.map (uapply env) l_l)
  | Mul l_l -> Mul (List.map (uapply env) l_l)
  | _ as unchanged -> unchanged

let apply env lit = iter_fun (fun l -> Printf.printf "%s\n" (show l) ; uapply env l) lit equal

let canonic_form env lit =
  let work lit = lit
    |> apply env
    |> (fun lit -> Printf.printf "apply %s\n" (show lit); lit)
    |> agg
    |> (fun lit -> Printf.printf "agg %s\n" (show lit); lit)
    |> expansion
    |> (fun lit -> Printf.printf "expansion %s\n" (show lit); lit)
    |> factorize
    |> (fun lit -> Printf.printf "||||> OUT %s\n" (show lit); lit)
  in
  iter_fun work lit equal

let canonic lit = canonic_form StrMap.empty lit

let positive = function
  | Lit i -> i >= 0
  | _ -> assert false

let resolve_0 lit =
  let rec loop l out =
    match l with
    | Var x -> Some (x, out)
    | Lit i ->
      if i = out then
        None
      else
        raise Bad_equation
    | Add l_l ->
      let i_l, l_l' = separate l_l in
      let i = List.fold_left (fun out i -> out + i) 0 i_l in
      loop (canonic (Add l_l')) (out - i)
    | Mul l_l ->
      let i_l, l_l' = separate l_l in
      let i = List.fold_left (fun out i -> i * out) 1 i_l in
      loop (canonic (Mul l_l')) (out / i)
    | Unit -> raise Bad_equation
  in loop lit 0
