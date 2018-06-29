open Util

(* module S = Ast *)
module S = Simpl

type inst_pot =
  | IPPot of string
  | IPLit of int
  | IPSize of string
  | IPLen of string
  | IPNode of string
  | IPDepth of string
  | IPAdd of inst_pot list
(*  | IPMin of inst_pot*)
  | IPMul of inst_pot list
  | IPUnit
[@@deriving show { with_path = false }]

let hash_s s =
  let out = ref 0 in
  for i = 0 to String.length s - 1 do
    out := !out + (Char.code s.[i])
  done;
  !out

let rec compare_pot_l p_l p_l' out =
  match p_l, p_l' with
  | [], [] -> out
  | [], rem -> out - List.length rem
  | rem, [] -> out + List.length rem
  | h::t, h'::t' -> compare_pot_l t t' (out + compare_pot h h')
and compare_pot p p' =
  match p, p' with
  | IPPot v, IPPot v' ->
    let h = hash_s v and h'= hash_s v' in
    if h > h' then 1 else if h < h' then -1 else 0
  | IPLit i, IPLit i' -> compare i i'
  | IPAdd p_l, IPAdd p_l' | IPMul p_l, IPMul p_l' -> compare_pot_l p_l p_l' 0
  | IPUnit, IPUnit -> 0
  | IPMul _, _ -> 1
  | IPAdd _, IPMul _ -> -1
  | IPAdd _, IPPot _ | IPAdd _, IPLit _ -> 1
  | IPPot _, IPMul _ | IPPot _, IPAdd _ -> -1
  | IPPot _, IPLit _ -> 1
  | IPLit _, _ -> -1
  | _ -> 0

(*let rgn_of = function
  | S.RRgn r -> r
  | S.RAlpha r -> r
*)
let rgn_of r = r

let show_out out =
  StrMap.fold (fun k pot out -> Printf.sprintf "%s%s : %s\n" out k (show_inst_pot pot)) out ""


let rec apply_p env = function
  | IPPot var when StrMap.mem var env ->
    Printf.printf "DEBUG1 %s\n" var;
    StrMap.find var env
  | IPAdd p_l -> IPAdd (List.map (apply_p env) p_l)
  | IPMul p_l -> IPMul (List.map (apply_p env) p_l)
  | _ as out -> out

let apply env pot_l =
  let work pot_l = StrMap.map (apply_p env) pot_l in
  iter_fun work pot_l

let separate p_l =
  let rec loop p_l out_i out_p =
    match p_l with
    | p::p_l' -> begin
      match p with
      | IPLit i -> loop p_l' (i::out_i) out_p
      | _ -> loop p_l' out_i (p::out_p)
    end
    | [] -> out_i, out_p
  in loop p_l [] []

let rec order_p = function
  | IPAdd p_l -> IPAdd (List.sort compare_pot p_l)
  | IPMul p_l -> IPMul (List.sort compare_pot p_l)
  | _ as unchanged -> unchanged

let order pot_l = StrMap.map order_p pot_l

let rec simplify_p = function
  | IPAdd [] -> IPLit 0
  | IPMul [] -> IPLit 1
  | IPAdd [p] | IPMul [p] -> p
  | IPAdd p_l -> IPAdd (List.filter (fun p -> p <> IPUnit && p <> IPLit 0) (List.map simplify_p p_l))
  | IPMul p_l ->
    if List.mem (IPLit 0) p_l then
      IPLit 0
    else
      IPMul (List.filter (fun p -> p <> IPUnit) (List.map simplify_p p_l))
  | _ as unchanged -> unchanged

let simplify pot_l =
  let work pot_l = StrMap.map simplify_p pot_l in
  order (iter_fun work pot_l)

let rec agg_p = function
  | IPAdd p_l ->
    let p_l' =
      List.fold_left
        (fun out p ->
          match agg_p p with
          | IPAdd p_l' -> List.rev_append p_l' out
          | _ as p'-> p'::out)
        [] p_l
    in
    let i_l, p_l = separate p_l' in
    let i = List.fold_left (fun out i -> out + i) 0 i_l in
    IPAdd ((IPLit i)::p_l)
  | IPMul p_l ->
    let p_l' =
      List.fold_left
        (fun out p ->
          match agg_p p with
          | IPMul p_l' -> List.rev_append p_l' out
          | _ as p' -> p'::out)
        [] p_l
    in
    let i_l, p_l = separate p_l' in
    let i = List.fold_left (fun out i -> out * i) 1 i_l in
    IPMul ((IPLit i)::p_l)
  | _ as out -> out

let agg pot_l = simplify (StrMap.map agg_p pot_l)

let rec expansion_p = function
  | IPMul p_l as unchanged ->
    let p_l = List.map expansion_p p_l in
    let lit_l, op_l = separate p_l in
    if op_l <> [] then begin
      match List.hd op_l with
      | IPAdd p_a ->
        IPAdd (List.map (fun p -> IPMul (List.rev_append (List.map (fun i -> IPLit i) lit_l) [p])) p_a)
      | _ -> IPMul p_l
    end else
      unchanged
  | IPAdd p_l -> IPAdd (List.map expansion_p p_l)
  | _ as unchanged -> unchanged

let expansion pot_l = agg (StrMap.map expansion_p pot_l)

let fact p p' =
  match p, p' with
  | IPPot v, IPPot v' when v = v' -> p, IPLit 2
  | IPPot v, IPMul p_l | IPMul p_l, IPPot v ->
    if List.mem (IPPot v) p_l then
      p, IPAdd ((IPLit 1)::(List.filter (fun p -> p <> IPPot v) p_l))
    else
      IPUnit, IPUnit
  | IPMul p_l, IPMul p_l' -> begin
    let pot_p = List.filter (function |IPPot _ -> true | _ -> false) p_l in
    let pot_p' = List.filter (function |IPPot _ -> true | _ -> false) p_l' in
    match List.filter (fun p -> List.mem p pot_p') pot_p with
    |[] -> IPUnit, IPUnit
    |p_com::_ ->
      let not_p_com p = p <> p_com in
      p_com, IPAdd [IPMul (List.filter (fun p -> p <> p_com) p_l) ; IPMul (List.filter (fun p -> p <> p_com) p_l')]
  end
  | _ -> IPUnit, IPUnit

let rec factorize_p = function
  | IPAdd p_l ->
    let p_l = List.map factorize_p p_l in
    let rec loop_p p p_l out =
      match p_l with
      | [] -> None
      | p'::p_l' -> begin
        match fact p p' with
        | IPUnit, IPUnit -> loop_p p p_l' (p'::out)
        | f, add_p -> Some (List.rev_append p_l' ((IPMul [f ; add_p])::out))
      end
    in
    let rec loop p_l out =
      match p_l with
      | [] -> out
      | p::p_l' -> begin
        match loop_p p p_l' [] with
        | None -> loop p_l' (p::out)
        | Some p_l'' -> List.rev_append out p_l''
      end
    in
    IPAdd (loop p_l [])
  | IPMul p_l -> IPMul (List.map factorize_p p_l)
  | _ as unchanged -> unchanged

let factorize pot_l =
  let work pot_l = pot_l |> StrMap.map factorize_p |> (fun out -> Printf.printf "factorize\n%s\n" (show_out out) ; out) |> agg in
  iter_fun work pot_l

let canonic_form env pot_l =
  let work pot_l =
    pot_l
    |> (fun out -> Printf.printf "canonic_form\n%s\n" (show_out out) ; print_newline (); out)
    |> apply env |> agg |> expansion |> agg |> factorize |> agg in
  iter_fun work pot_l

let rec remove_p = function
  | IPPot _ -> IPLit 0
  | IPAdd p_l -> IPAdd (List.map remove_p p_l)
  | IPMul p_l -> IPMul (List.map remove_p p_l)
  | _ as unchanged -> unchanged

let remove pot_l = StrMap.map remove_p pot_l

let positive_p = function
  | IPLit i -> i >= 0
  | _ -> assert false

let positive pot_l = StrMap.for_all (fun _ p -> positive_p p) pot_l

let rec pot_of env t =
  match S.get_term t with
  | S.Var v -> begin
    Printf.printf "DEBUG2 %s\n" v;
    env, try StrMap.find v env with Not_found -> IPPot v
  end
  | S.Letrec (v, t1, t2) | S.Let (v, t1, t2) ->
    let env, pot_t1 = pot_of env t1 in
    pot_of (StrMap.add v pot_t1 env) t2
  | S.MatchList (var_match, t_nil, x, xs, t_cons) ->
    let env, pot_t_nil = pot_of env t_nil in
    let env' = StrMap.add x IPUnit (StrMap.add xs (IPAdd [IPPot var_match ; IPLit (-1)]) env) in
    pot_of env' t_cons
  | S.MatchTree (var_match, t_leaf, x, tl, tr, t_node) ->
    Printf.printf "AQUI\n";
    let env, pot_t_leaf = pot_of env t_leaf in
    let env' = StrMap.add x IPUnit (StrMap.add var_match (IPAdd [IPPot tl ; IPPot tr ; IPLit 1]) env) in
    pot_of env' t_node
  | S.Pair (t1, t2, t3) -> pot_of env t1
  | S.Fst t1 -> pot_of env t1
  | S.Snd t1 -> pot_of env t1
  | S.Hd t1 -> pot_of env t1
  | S.Tl t1 ->
    let env, pot_t1 = pot_of env t1 in
    env, IPAdd [pot_t1 ; IPLit (-1)]
  | S.Nil -> env, IPLit 0
  | S.Cons (t1, t2, t3) ->
    let env, pot_t2 = pot_of env t2 in
    env, IPAdd[pot_t2 ; IPLit 1]
  | S.Leaf -> env, IPLit 0
  | S.Node (t1, t2, t3, t4) -> pot_of env t1
  | S.Ref (t1, t2) -> pot_of env t1
  | S.Assign (t1, t2) -> pot_of env t1
  | S.Deref t1 -> pot_of env t1
  | S.Newrgn -> env, IPUnit
  | S.Aliasrgn (t1, t2) -> pot_of env t1
  | S.Freergn t1 -> pot_of env t1
  | S.Sequence (t1, t2) -> pot_of env t1
  | _ -> env, IPUnit

let rec instanciate pot arg_l =
  let subs i = List.nth arg_l i in
  match pot with
  | S.PPot id -> IPPot id
  | S.PLit i ->  IPLit i
  | S.PSize i -> IPPot (subs i)
  | S.PLen i -> IPPot (subs i)
  | S.PNode i -> IPPot (subs i)
  | S.PDepth i -> IPPot (subs i)
  | S.PAdd (p1, p2) -> IPAdd [instanciate p1 arg_l ; instanciate p2 arg_l]
  | S.PMin p1 -> IPMul [IPLit (-1) ; instanciate p1 arg_l]
  | S.PMul (p1, p2) -> IPMul [instanciate p1 arg_l ; instanciate p2 arg_l]
  | S.PUnit -> IPUnit

let add_to_env x mty env =
  let add_ls x = function
    | Some i -> StrMap.add x (IPLit i) env
    | None -> StrMap.add x (IPPot (mk_var ())) env
  in
  match mty with
  | S.TList (ls, mty1, r) -> add_ls x ls
  | S.TTree (lsn, lsd, mty1, r) -> add_ls x lsn
  | _ -> env

let rec verify_t t env s_pot_l out =
  let te = S.get_term t in
  let mty = S.get_type t in
  match te with
  | S.Binop (_, t1, t2) | S.Comp (_, t1, t2) ->
    verify_t t1 env s_pot_l (verify_t t2 env s_pot_l out)
  | S.Not t1 -> verify_t t1 env s_pot_l out
  | S.Neg t1 -> verify_t t1 env s_pot_l out
  | S.Fun (s, arg_l, t1, t2, f_pot) -> begin
    match f_pot with
    | None -> assert false
    | Some pot_l' ->
      if verify s arg_l t1 (StrMap.add s pot_l' s_pot_l) then
        out
      else
        raise (S.Verify_Error (Printf.sprintf "Wrong potential annotations for function %s\n" s))
    end
  | S.App (t1, arg_l) ->
    let pot_l =
      match S.get_term t1 with
      | S.Var v -> StrMap.find v s_pot_l
      | S.Fun (_, arg_l, _, _, Some(pot_l)) -> pot_l
      | _ -> assert false
    in
    (*Printf.printf "%s\n" (S.show_fun_pot_desc pot_l);*)
    let out = verify_t t1 env s_pot_l out in
    List.map
      (fun out_p ->
        List.fold_left
          (fun out_p (r, pot) ->
            let pot' = instanciate (fst pot) arg_l in
            StrMap.add r (try IPAdd [StrMap.find r out_p ; pot'] with Not_found -> pot') out_p)
          out_p pot_l)
      out
  | S.If (t1, t2, t3) ->
  verify_t t3 env s_pot_l (verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out))
  | S.MatchList (_, t_nil, x, xs, t_cons) ->
    let out_nil = verify_t t_nil env s_pot_l out in
    let out_cons = verify_t t_cons env s_pot_l out in
    List.rev_append out_nil out_cons
  | S.MatchTree (_, t_leaf, x, tl, tr, t_node) ->
    let out_leaf = verify_t t_leaf env s_pot_l out in
    let out_node = verify_t t_node env s_pot_l out in
    List.rev_append out_leaf out_node
  | S.Let (x, t1, t2) ->
    let env' = add_to_env x (S.get_type t1) env in
    verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out)
  | S.Letrec (x, t1, t2) ->
    let S.Fun(_, _, _, _, Some pot_l) = S.get_term t1 in
    let s_pot_l' = StrMap.add x pot_l s_pot_l in
    verify_t t2 env s_pot_l' (verify_t t1 env s_pot_l out)
  | S.Pair (t1, t2, t3) ->
    let S.TCouple(_, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t t3 env s_pot_l (verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out)) in
    List.map
      (fun out_p ->
        let pot_r = try StrMap.find r out_p with Not_found -> IPUnit in
        StrMap.add r (IPAdd [pot_r ; IPLit (cost_of RPAIR)]) out_p)
      out
  | S.Fst t1 ->
    verify_t t1 env s_pot_l out
  | S.Snd t1 ->
    verify_t t1 env s_pot_l out
  | S.Hd t1 ->
    verify_t t1 env s_pot_l out
  | S.Tl t1 ->
    verify_t t1 env s_pot_l out
  | S.Nil -> out
  | S.Cons (t1, t2, t3) ->
    let S.TList(_, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t t3 env s_pot_l (verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out)) in
    List.map
      (fun out_p ->
        let pot_r = try StrMap.find r out_p with Not_found -> IPUnit in
        StrMap.add r (IPAdd [pot_r ; IPLit (cost_of RCONS)]) out_p)
      out
  | S.Leaf -> out
  | S.Node (t1, t2, t3, t4) ->
    let S.TTree(_, _, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t t4 env s_pot_l (verify_t t3 env s_pot_l (verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out))) in
    List.map
      (fun out_p ->
        let pot_r = try StrMap.find r out_p with Not_found -> IPUnit in
        StrMap.add r (IPAdd [pot_r ; IPLit (cost_of RNODE)]) out_p)
      out
  | S.Ref (t1, t2) ->
    let S.TRef(_, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out) in
    List.map
      (fun out_p ->
        let pot_r = try StrMap.find r out_p with Not_found -> IPUnit in
        StrMap.add r (IPAdd [pot_r ; IPLit (cost_of RREF)]) out_p)
      out
  | S.Assign (t1, t2) -> verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out)
  | S.Deref t1 -> verify_t t1 env s_pot_l out
  | S.Newrgn -> out
  | S.Aliasrgn (t1, t2) -> verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out)
  | S.Freergn t1 -> verify_t t1 env s_pot_l out
  | S.Sequence (t1, t2) -> verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out)
  | _ -> out

and verify f arg_l t s_pot_l =
  let f_pot =
    List.fold_left
      (fun out (rgn, (p1, p2)) -> StrMap.add rgn (instanciate p1 arg_l) out)
      StrMap.empty (StrMap.find f s_pot_l)
  in
  let out = verify_t t StrMap.empty s_pot_l [StrMap.empty] in
  let env = List.fold_left (fun env x -> StrMap.add x (IPPot x) env) StrMap.empty arg_l in
  let env, _ = pot_of env t in
  Printf.printf "ENV : %s\n" (strmap_str env show_inst_pot);
  List.iter (fun pot_l -> Printf.printf "verified\n%s\n" (show_out pot_l)) out;
  Printf.printf "annotated\n%s\n" (show_out f_pot);
  let out = List.map (canonic_form env) out in
  let f_pot = canonic_form env f_pot in
  List.iter (fun pot_l -> Printf.printf "verified\n%s\n" (show_out pot_l)) out;
  Printf.printf "annotated\n%s\n" (show_out f_pot);
  let cpot =
    List.map
      (fun out_p ->
        StrMap.mapi
          (fun r pot ->
            try
              let pot_p = StrMap.find r out_p in
              IPAdd [pot ; IPMul [IPLit (-1) ; pot_p]]
            with Not_found -> pot)
          f_pot)
      out
  in
  List.iter (fun pot_l -> Printf.printf "compared1\n%s\n" (show_out pot_l)) cpot;
  let cpot = List.map (canonic_form env) cpot in
  List.iter (fun pot_l -> Printf.printf "compared2\n%s\n" (show_out pot_l)) cpot;
  let cpot = List.map (fun pot_l -> canonic_form env (remove pot_l)) cpot in
  List.iter (fun pot_l -> Printf.printf "compared3\n%s\n" (show_out pot_l)) cpot;
  List.for_all positive cpot

let rec process t =
  let te = S.get_term t in
  let mty = S.get_type t in
  let alpha_l = S.get_alpha_l t in
  let rgn_l = S.get_rgn_l t in
  S.mk_term
    (match te with
     | S.Binop (op, t1, t2) -> S.Binop (op, process t1, process t2)
     | S.Not t1 -> S.Not (process t1)
     | S.Neg t1 -> S.Neg (process t1)
     | S.Comp (op, t1, t2) -> S.Comp (op, process t1, process t2)
     | S.Fun (s, arg_l, t1, t2, f_pot) -> begin
       match f_pot with
       | None -> S.Fun (s, arg_l, process t1, process t2, f_pot)
       | Some pot_l ->
         if verify s arg_l t1 (StrMap.singleton s pot_l) then
           S.Fun (s, arg_l, process t1, process t2, f_pot)
         else
           raise (S.Verify_Error (Printf.sprintf "Wrong potential annotations for function %s\n" s))
     end
     | S.App (t1, arg_l) -> S.App (process t1, arg_l)
     | S.If (t1, t2, t3) -> S.If (process t1, process t2, process t3)
     | S.MatchList (var_match, t2, x, xs, t3) -> S.MatchList (var_match, process t2, x, xs, process t3)
     | S.MatchTree (var_match, t2, x, tl, tr, t3) -> S.MatchTree (var_match, process t2, x, tl, tr, process t3)
     | S.Let (x, t1, t2) -> S.Let (x, process t1, process t2)
     | S.Letrec (x, t1, t2) -> S.Letrec (x, process t1, process t2)
     | S.Pair (t1, t2, t3) -> S.Pair (process t1, process t2, process t3)
     | S.Fst t1 -> S.Fst (process t1)
     | S.Snd t1 -> S.Snd (process t1)
     | S.Hd t1 -> S.Hd (process t1)
     | S.Tl t1 -> S.Tl (process t1)
     | S.Cons (t1, t2, t3) -> S.Cons (process t1, process t2, process t3)
     | S.Node (t1, t2, t3, t4) -> S.Node (process t1, process t2, process t3, process t4)
     | S.Ref (t1, t2) -> S.Ref (process t1, process t2)
     | S.Assign (t1, t2) -> S.Assign (process t1, process t2)
     | S.Deref t1 -> S.Deref (process t1)
     | S.Aliasrgn (t1, t2) -> S.Aliasrgn (process t1, process t2)
     | S.Freergn t1 -> S.Freergn (process t1)
     | S.Sequence (t1, t2) -> S.Sequence (process t1, process t2)
     | _ -> te)
    mty alpha_l rgn_l
