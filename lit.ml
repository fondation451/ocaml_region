(* Litteral Expressions Management *)

open Util

exception Bad_equation

type t =
  | Var of string
  | Lit of int
  | Add of t list
  | Mul of t list
  | RShift of t
  | Unit
[@@deriving show { with_path = false }]

let rec equal l l' =
  match l, l' with
  | Var v, Var v' -> v = v'
  | Lit i, Lit i' -> i = i'
  | Add l_l, Add l_l' | Mul l_l, Mul l_l' ->
    let rec loop ll ll' =
      match ll with
      | [] -> ll' = []
      | h::t ->
        if List.exists (equal h) ll' then
          let lh, lnh = List.partition (equal h) ll' in
          loop t (List.rev_append (List.tl lh) lnh)
        else
          false
    in
    let out = loop l_l l_l' in
(*    Printf.printf "Are they equal ? %s    %s        %b\n\n" (show l) (show l') out ;*)
    out
  | RShift l1, RShift l2 -> equal l1 l2
  | Unit, Unit -> true
  | _ ->
(*          Printf.printf "Not EQUAL %s %s\n\n" (show l) (show l');*)
  false

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
  | RShift l1, RShift l2 -> compare l1 l2
  | Unit, Unit -> 0
  | Mul _, _ -> 1
  | Add _, Mul _ -> -1
  | Add _, Var _ | Add _, Lit _ -> 1
  | Var _, Mul _ | Var _, Add _ -> -1
  | Var _, Lit _ -> 1
  | _, RShift _ -> 1
  | Lit _, _ -> -1
  | _ -> 0

let fv lit =
  let rec loop lit out =
    match lit with
    | Var v -> StrSet.add v out
    | Add l_l | Mul l_l -> List.fold_left (fun out l -> loop l out) out l_l
    | RShift l -> loop l out
    | _ -> out
  in loop lit StrSet.empty

let rec order = function
  | Add p_l -> Add (List.sort compare p_l)
  | Mul p_l -> Mul (List.sort compare p_l)
  | RShift l -> RShift (order l)
  | _ as unchanged -> unchanged

let simplify lit =
  let rec loop = function
    | Add [] -> Lit 0
    | Mul [] -> Lit 1
    | Add [l] | Mul [l] -> l
    | Add l_l ->
      let l_l' = List.filter (fun l -> l <> Unit) (List.map loop l_l) in
      if l_l' <> l_l then
(*        (Printf.printf "Aqui delante %s %s!!!\n\n"
        (List.fold_left (fun out l -> out ^ ", " ^ (show l)) "" l_l')
        (List.fold_left (fun out l -> out ^ ", " ^ (show l)) "" l_l) ;*)
        loop (Add l_l')
      else
        let l_l' = List.filter (fun l -> l <> Lit 0) (List.map loop l_l) in
        let rl_l, l_l' = List.partition (fun l -> match l with RShift _ -> true | _ -> false) l_l' in
        let rl_l' = List.map (fun (RShift rl) -> rl) rl_l in
        if rl_l' <> [] then
          let l_l' = List.map (fun l -> Mul [l ; Lit 2]) l_l' in
          loop (RShift (Add (List.rev_append rl_l' l_l')))
        else
          Add l_l'
    | Mul l_l ->
      if List.mem (Lit 0) l_l then
        Lit 0
      else
        let l_l' = List.filter (fun l -> l <> Unit) (List.map loop l_l) in
        let rl_l, l_l' = List.partition (fun l -> match l with RShift _ -> true | _ -> false) l_l' in
        let l_l' = List.fold_left (fun out (RShift rl) -> rl::out) l_l' rl_l in
        List.fold_left (fun out _ -> RShift out) (Mul l_l') rl_l
    | RShift l -> begin
      match loop l with
      | Lit i -> Lit (i asr 1)
      | Mul l_l when List.mem (Lit 2) l_l -> Mul (List.filter (fun l' -> l' <> Lit 2) l_l)
      | _ as other -> RShift other
    end
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
    | RShift l -> RShift (loop l)
    | _ as out -> out
  in
  let out = loop (simplify lit) in
(*  Printf.printf "agg loop %s\n" (show out);*)
  simplify out

let rec exp l_l out =
  match l_l with
  | [] -> out
  | [l] -> l::out
  | l::(l'::t as l_l') -> begin
    match l, l' with
    | f, Add add_l | Add add_l, f -> List.rev_append ((Add (List.map (fun lit -> Mul [lit ; f]) add_l))::t) out
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
(*  Printf.printf "expansion loop %s\n" (show out);*)
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
  | RShift l -> RShift (uapply env l)
  | _ as unchanged -> unchanged

let apply env lit = iter_fun (fun l -> (*Printf.printf "%s\n" (show l) ;*) uapply env l) lit equal

let canonic_form env lit =
  let work lit = lit
(*    |> (fun lit -> Printf.printf "||||> IN %s\n" (show lit); lit)*)
    |> apply env
(*    |> (fun lit -> Printf.printf "apply %s\n" (show lit); lit)*)
    |> agg
(*    |> (fun lit -> Printf.printf "agg %s\n" (show lit); lit)*)
    |> expansion
(*    |> (fun lit -> Printf.printf "expansion %s\n" (show lit); lit)*)
    |> factorize
(*    |> (fun lit -> Printf.printf "||||> OUT %s\n" (show lit); lit)*)
  in
  iter_fun work lit (fun l l'-> (*Printf.printf "%s\n?=\n%s\n" (show l) (show l') ;*) equal l l')

let canonic lit = canonic_form StrMap.empty lit

let positive = function
  | Lit i -> i >= 0
  | _ -> assert false

let resolve_0 lit =
  let rec loop l old out =
    if l = old then
      None
    else
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
      loop (canonic (Add l_l')) l (out - i)
    | Mul l_l ->
      let i_l, l_l' = separate l_l in
      let i = List.fold_left (fun out i -> i * out) 1 i_l in
      loop (canonic (Mul l_l')) l (out / i)
    | RShift l -> loop l lit (2*out)
    | Unit -> raise Bad_equation
  in loop lit Unit 0

let from_int i = Lit i
let add l l' = canonic (Add [l ; l'])
let sub l l' = canonic (Add [l ; Mul [Lit (-1) ; l']])
let mul l l' = canonic (Mul [l ; l'])

(*
let rec max l l' =
  match l, l' with
  | Var of string
  | Lit i, Lit i' -> Lit (Pervasives.max i i')
  | Add of t list
  | Mul of t list
  | RShift ll, RShift ll' -> RShift (max ll ll')
  | Unit, (_ as out) | (_ as out), Unit -> out
*)
