open Util

module S = Simpl

let rgn_of r = r

let show_out out =
  StrMap.fold (fun k pot out -> Printf.sprintf "%s%s : %s\n" out k (Lit.show pot)) out ""

let rec remove_p = function
  | Lit.Var _ -> Lit.Lit 1000
  | Lit.Add p_l -> Lit.Add (List.map remove_p p_l)
  | Lit.Mul p_l -> Lit.Mul (List.map remove_p p_l)
  | Lit.RShift l -> Lit.RShift (remove_p l)
  | _ as unchanged -> unchanged

let remove lit_l = StrMap.map remove_p lit_l
let positive lit_l = StrMap.for_all (fun _ l -> Lit.positive l) lit_l
let order lit_l = StrMap.map Lit.order lit_l
let simplify_lit_l lit_l = StrMap.map Lit.simplify lit_l
let agg lit_l = StrMap.map Lit.agg lit_l
let expansion lit_l = StrMap.map Lit.expansion lit_l
let factorize lit_l = StrMap.map Lit.factorize lit_l
let apply env lit_l = StrMap.map (Lit.apply env) lit_l
let canonic_form env lit_l = StrMap.map (Lit.canonic_form env) lit_l
let canonic lit_l = StrMap.map (Lit.canonic) lit_l

let rec pot_of env t =
  match S.get_term t with
  | S.Var v -> begin
    env, try StrMap.find v env with Not_found -> Lit.Var v
  end
  | S.Letrec (v, t1, t2) | S.Let (v, t1, t2) ->
    let env, pot_t1 = pot_of env t1 in
    pot_of (StrMap.add v pot_t1 env) t2
  | S.MatchList (var_match, t_nil, x, xs, t_cons) ->
    let env, pot_t_nil = pot_of env t_nil in
    let env' = StrMap.add x Lit.Unit (StrMap.add xs (Lit.Add [Lit.Var var_match ; Lit.Lit (-1)]) env) in
    pot_of env' t_cons
  | S.MatchTree (var_match, t_leaf, x, tl, tr, t_node) ->
    Printf.printf "AQUI\n";
    let env, pot_t_leaf = pot_of env t_leaf in
    let env' = StrMap.add x Lit.Unit (StrMap.add var_match (Lit.Add [Lit.Var tl ; Lit.Var tr ; Lit.Lit 1]) env) in
    pot_of env' t_node
  | S.Pair (t1, t2, t3) -> pot_of env t1
  | S.Fst t1 -> pot_of env t1
  | S.Snd t1 -> pot_of env t1
  | S.Hd t1 -> pot_of env t1
  | S.Tl t1 ->
    let env, pot_t1 = pot_of env t1 in
    env, Lit.Add [pot_t1 ; Lit.Lit (-1)]
  | S.Nil -> env, Lit.Lit 0
  | S.Cons (t1, t2, t3) ->
    let env, pot_t2 = pot_of env t2 in
    env, Lit.Add[pot_t2 ; Lit.Lit 1]
  | S.Leaf -> env, Lit.Lit 0
  | S.Node (t1, t2, t3, t4) -> pot_of env t1
  | S.Ref (t1, t2) -> pot_of env t1
  | S.Assign (t1, t2) -> pot_of env t1
  | S.Deref t1 -> pot_of env t1
  | S.Newrgn -> env, Lit.Unit
  | S.Aliasrgn (t1, t2) -> pot_of env t1
  | S.Freergn t1 -> pot_of env t1
  | S.Sequence (t1, t2) -> pot_of env t1
  | _ -> env, Lit.Unit

let rec instanciate pot arg_l env =
  let type_of i = StrMap.find (List.nth arg_l i) env in
  match pot with
  | S.PPot id -> Lit.Var id
  | S.PLit i ->  Lit.Lit i
  | S.PSize i -> begin
    match type_of i with
    | S.TList (ls, _, _) | S.TTree (ls, _, _, _) -> ls
    | _ -> assert false
  end
  | S.PLen i -> begin
    match type_of i with
    | S.TList (ls, _, _) -> ls
    | _ -> assert false
  end
  | S.PNode i -> begin
    match type_of i with
    | S.TTree (lsn, _, _, _) -> lsn
    | _ -> assert false
  end
  | S.PDepth i -> begin
    match type_of i with
    | S.TTree (_, lsd, _, _) -> lsd
    | _ -> assert false
  end
  | S.PAdd (p1, p2) -> Lit.Add [instanciate p1 arg_l env ; instanciate p2 arg_l env]
  | S.PMin p1 -> Lit.Mul [Lit.Lit (-1) ; instanciate p1 arg_l env]
  | S.PMul (p1, p2) -> Lit.Mul [instanciate p1 arg_l env ; instanciate p2 arg_l env]
  | S.PUnit -> Lit.Unit

let add_to_env x mty env =
  let add_ls x = function
    | Lit.Lit i -> StrMap.add x (Lit.Lit i) env
    | _ -> StrMap.add x (Lit.Var (mk_var ())) env
  in
  match mty with
  | S.TList (ls, mty1, r) -> add_ls x ls
  | S.TTree (lsn, lsd, mty1, r) -> add_ls x lsn
  | _ -> env

let strpot_l (mty_arg_l, pot_l) =
  Printf.sprintf "%s, %s" (List.fold_left (fun out mty -> out ^ ", " ^ (S.show_rcaml_type mty)) "" mty_arg_l) (S.show_fun_pot_desc pot_l)

let substition_r f_mty_arg_l mty_arg_l =
  List.fold_left2
    (fun out f_mty mty ->
      match f_mty, mty with
      | S.THnd r, S.THnd r' -> StrMap.add r r' out
      | _ -> out)
    StrMap.empty f_mty_arg_l mty_arg_l

let substitute_r f_mty_arg_l mty_arg_l pot_l =
  let s = substition_r f_mty_arg_l mty_arg_l in
  StrMap.bindings
    (List.fold_left
      (fun out (r, (pot1, pot2)) ->
        let r = try StrMap.find r s with Not_found -> r in
        let (pot1', pot2') = try StrMap.find r out with Not_found -> S.PUnit, S.PUnit in
        StrMap.add r (S.PAdd (pot1, pot1'), S.PAdd (pot2, pot2')) out)
      StrMap.empty pot_l)

let rec verify_t env t s_pot_l out =
  Printf.printf "--------- VERIFY_T ------------\n%s\n\n" (S.show_typed_term t);
  let te = S.get_term t in
  let mty = S.get_type t in
  match te with
  | S.Binop (_, t1, t2) | S.Comp (_, t1, t2) -> verify_t env t1 s_pot_l (verify_t env t2 s_pot_l out)
  | S.Not t1 -> verify_t env t1 s_pot_l out
  | S.Neg t1 -> verify_t env t1 s_pot_l out
  | S.Fun (s, arg_l, t1, t2, f_pot) -> begin
    let S.TFun (mty_arg_l, _, _) = mty in
    let env = List.fold_left2 (fun env arg mty_a -> StrMap.add arg mty_a env) env arg_l mty_arg_l in
    match f_pot with
    | None -> assert false
    | Some pot_l' ->
      if verify s arg_l t1 (StrMap.add s (mty_arg_l, pot_l') s_pot_l) then
        out
      else
        raise (S.Verify_Error (Printf.sprintf "Wrong potential annotations for function %s\n" s))
    end
  | S.App (t1, arg_l) ->
    let pot_l =
      match S.get_term t1 with
      | S.Var v ->
        let S.TFun (mty_arg_l, _, _) = S.get_type t1 in
        let f_mty_arg_l, pot_l = Printf.printf "@@@@@@@@@@@@ %s\n\n" v ;StrMap.find v s_pot_l in
        substitute_r f_mty_arg_l mty_arg_l pot_l
      | S.Fun (_, arg_l, _, _, Some(pot_l)) -> pot_l
      | _ -> assert false
    in
    (*Printf.printf "%s\n" (S.show_fun_pot_desc pot_l);*)
    let out = verify_t env t1 s_pot_l out in
    List.map
      (fun (s, out_p) ->
        List.fold_left
          (fun (s, out_p) (r, pot) ->
            let pot' = instanciate (fst pot) arg_l env in
            s, StrMap.add r (try Lit.Add [StrMap.find r out_p ; pot'] with Not_found -> pot') out_p)
          (s, out_p) pot_l)
      out
  | S.If (t1, t2, t3) ->
  verify_t env t3 s_pot_l (verify_t env t2 s_pot_l (verify_t env t1 s_pot_l out))
  | S.MatchList (l, t_nil, x, xs, t_cons) ->
    let out_nil = verify_t env t_nil s_pot_l out in
    let S.TList (ls, mty_x, r) = Printf.printf "DEBUG AQUI !!!!\n\n";StrMap.find l env in
    let mty_xs = S.TList (Lit.Add [ls ; Lit.Lit (-1)], mty_x, r) in
    let env = StrMap.add x mty_x (StrMap.add xs mty_xs env) in
    let out_cons = verify_t env t_cons s_pot_l out in
    let Lit.Var vls = ls in
    let out_nil = List.map (fun (s, pot_l) -> StrMap.add vls (Lit.Lit 0) s, pot_l) out_nil in
    List.rev_append out_nil out_cons
  | S.MatchTree (t, t_leaf, x, tl, tr, t_node) ->
    let out_leaf = verify_t env t_leaf s_pot_l out in
    let S.TTree (lsn, lsd, mty_x, r) = StrMap.find t env in
    let mty_tf = S.TTree (Lit.RShift (Lit.Add [lsn ; Lit.Lit (-1)]), Lit.Add [lsd ; Lit.Lit (-1)], mty_x, r) in
    let env = StrMap.add x mty_x (StrMap.add tl mty_tf (StrMap.add tr mty_tf env)) in
    let out_node = verify_t env t_node s_pot_l out in
    let Lit.Var vlsn = lsn in
    let Lit.Var vlsd = lsd in
    let out_leaf = List.map (fun (s, pot_l) -> StrMap.add vlsn (Lit.Lit 0) (StrMap.add vlsd (Lit.Lit 0) s), pot_l) out_leaf in
    List.rev_append out_leaf out_node
  | S.Let (x, t1, t2) ->
    let env' = StrMap.add x (S.get_type t1) env in
    verify_t env' t2 s_pot_l (verify_t env t1 s_pot_l out)
  | S.Letrec (x, t1, t2) ->
    let env' = StrMap.add x (S.get_type t1) env in
    let S.Fun(_, _, _, _, Some pot_l) = S.get_term t1 in
    let S.TFun (mty_arg_l, _, _) = S.get_type t1 in
    let s_pot_l' = StrMap.add x (mty_arg_l, pot_l) s_pot_l in
    verify_t env' t2 s_pot_l' (verify_t env t1 s_pot_l out)
  | S.Pair (t1, t2, t3) ->
    let S.TCouple(_, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t env t3 s_pot_l (verify_t env t2 s_pot_l (verify_t env t1 s_pot_l out)) in
    List.map
      (fun (s, out_p) ->
        let pot_r = try StrMap.find r out_p with Not_found -> Lit.Unit in
        s, StrMap.add r (Lit.Add [pot_r ; Lit.Lit (cost_of RPAIR)]) out_p)
      out
  | S.Fst t1 ->
    verify_t env t1 s_pot_l out
  | S.Snd t1 ->
    verify_t env t1 s_pot_l out
  | S.Hd t1 ->
    verify_t env t1 s_pot_l out
  | S.Tl t1 ->
    verify_t env t1 s_pot_l out
  | S.Nil -> out
  | S.Cons (t1, t2, t3) ->
    let S.TList(_, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t env t3 s_pot_l (verify_t env t2 s_pot_l (verify_t env t1 s_pot_l out)) in
    List.map
      (fun (s, out_p) ->
        let pot_r = try StrMap.find r out_p with Not_found -> Lit.Unit in
        s, StrMap.add r (Lit.Add [pot_r ; Lit.Lit (cost_of RCONS)]) out_p)
      out
  | S.Leaf -> out
  | S.Node (t1, t2, t3, t4) ->
    let S.TTree(_, _, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t env t4 s_pot_l (verify_t env t3 s_pot_l (verify_t env t2 s_pot_l (verify_t env t1 s_pot_l out))) in
    List.map
      (fun (s, out_p) ->
        let pot_r = try StrMap.find r out_p with Not_found -> Lit.Unit in
        s, StrMap.add r (Lit.Add [pot_r ; Lit.Lit (cost_of RNODE)]) out_p)
      out
  | S.Ref (t1, t2) ->
    let S.TRef(_, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t env t2 s_pot_l (verify_t env t1 s_pot_l out) in
    List.map
      (fun (s, out_p) ->
        let pot_r = try StrMap.find r out_p with Not_found -> Lit.Unit in
        s, StrMap.add r (Lit.Add [pot_r ; Lit.Lit (cost_of RREF)]) out_p)
      out
  | S.Assign (t1, t2) -> verify_t env t2 s_pot_l (verify_t env t1 s_pot_l out)
  | S.Deref t1 -> verify_t env t1 s_pot_l out
  | S.Newrgn -> out
  | S.Aliasrgn (t1, t2) -> verify_t env t2 s_pot_l (verify_t env t1 s_pot_l out)
  | S.Freergn t1 -> verify_t env t1 s_pot_l out
  | S.Sequence (t1, t2) -> verify_t env t2 s_pot_l (verify_t env t1 s_pot_l out)
  | _ -> out

and verify f arg_l t s_pot_l =
  let mty_arg_l, f_pot = StrMap.find f s_pot_l in
  let env = List.fold_left2 (fun out arg mty_arg -> StrMap.add arg mty_arg out) StrMap.empty arg_l mty_arg_l in
  let f_pot =
    List.fold_left
      (fun out (rgn, (p1, p2)) -> StrMap.add rgn (instanciate p1 arg_l env) out)
      StrMap.empty f_pot
  in
  let out = verify_t env t s_pot_l [StrMap.empty, StrMap.empty] in
(*  let env = List.fold_left (fun env x -> StrMap.add x (Lit.Var x) env) StrMap.empty arg_l in*)
(*  let env, _ = pot_of env t in*)
  let f_pot = List.map (fun (s, _) -> s, f_pot) out in
  Printf.printf "VERIFY %s\n\n" f;
  Printf.printf "S_POT_L : %s\n\n" (strmap_str s_pot_l strpot_l) ;
(*  Printf.printf "ENV : %s\n" (strmap_str env Lit.show);*)
  List.iter (fun (s, pot_l) -> Printf.printf "verified\n%s\n%s\n" (strmap_str s Lit.show) (show_out pot_l)) out;
  List.iter (fun (s, pot_l) -> Printf.printf "annotated\n%s\n%s\n" (strmap_str s Lit.show) (show_out pot_l)) f_pot;
  let out = List.map (fun (s, pot_l) -> canonic_form s pot_l) out in
  let f_pot = List.map (fun (s, pot_l) -> canonic_form s pot_l) f_pot in
  List.iter (fun pot_l -> Printf.printf "verified\n%s\n" (show_out pot_l)) out;
  List.iter (fun pot_l -> Printf.printf "annotated\n%s\n" (show_out pot_l)) f_pot;
  let cpot =
    List.map2
      (fun f_pot_p_r out_p_r ->
        StrMap.mapi
          (fun r f_pot_p ->
            try
              let out_p = StrMap.find r out_p_r in
              Lit.Add [f_pot_p ; Lit.Mul [Lit.Lit (-1) ; out_p]]
            with Not_found -> f_pot_p)
          f_pot_p_r)
      f_pot out
  in
  List.iter (fun pot_l -> Printf.printf "compared1\n%s\n" (show_out pot_l)) cpot;
  let cpot = List.map (canonic) cpot in
  List.iter (fun pot_l -> Printf.printf "compared2\n%s\n" (show_out pot_l)) cpot;
  let cpot = List.map (fun pot_l -> canonic (remove pot_l)) cpot in
  List.iter (fun pot_l -> Printf.printf "compared3\n%s\n" (show_out pot_l)) cpot;
  List.for_all positive cpot

let rec process_t s_pot_l t =
  let te = S.get_term t in
  let mty = S.get_type t in
  let alpha_l = S.get_alpha_l t in
  let rgn_l = S.get_rgn_l t in
  S.mk_term
    (match te with
     | S.Binop (op, t1, t2) -> S.Binop (op, process_t s_pot_l t1, process_t s_pot_l t2)
     | S.Not t1 -> S.Not (process_t s_pot_l t1)
     | S.Neg t1 -> S.Neg (process_t s_pot_l t1)
     | S.Comp (op, t1, t2) -> S.Comp (op, process_t s_pot_l t1, process_t s_pot_l t2)
     | S.Fun (s, arg_l, t1, t2, f_pot) -> begin
       let S.TFun (mty_arg_l, _, _) = mty in
       match f_pot with
       | None -> S.Fun (s, arg_l, process_t s_pot_l t1, process_t s_pot_l t2, f_pot)
       | Some pot_l ->
         if verify s arg_l t1 (StrMap.add s (mty_arg_l, pot_l) s_pot_l) then
           S.Fun (s, arg_l, process_t s_pot_l t1, process_t s_pot_l t2, f_pot)
         else
           raise (S.Verify_Error (Printf.sprintf "Wrong potential annotations for function %s\n" s))
     end
     | S.App (t1, arg_l) -> S.App (process_t s_pot_l t1, arg_l)
     | S.If (t1, t2, t3) -> S.If (process_t s_pot_l t1, process_t s_pot_l t2, process_t s_pot_l t3)
     | S.MatchList (var_match, t2, x, xs, t3) -> S.MatchList (var_match, process_t s_pot_l t2, x, xs, process_t s_pot_l t3)
     | S.MatchTree (var_match, t2, x, tl, tr, t3) -> S.MatchTree (var_match, process_t s_pot_l t2, x, tl, tr, process_t s_pot_l t3)
     | S.Let (x, t1, t2) -> S.Let (x, process_t s_pot_l t1, process_t s_pot_l t2)
     | S.Letrec (x, t1, t2) ->
       let t1' = process_t s_pot_l t1 in
       let s_pot_l =
         match S.get_term t1', S.get_type t1' with
         | S.Fun (s, _, _, _, Some f_pot), S.TFun (mty_arg_l, _, _) -> StrMap.add s (mty_arg_l, f_pot) s_pot_l
         | _ -> s_pot_l
       in
       S.Letrec (x, t1, process_t s_pot_l t2)
     | S.Pair (t1, t2, t3) -> S.Pair (process_t s_pot_l t1, process_t s_pot_l t2, process_t s_pot_l t3)
     | S.Fst t1 -> S.Fst (process_t s_pot_l t1)
     | S.Snd t1 -> S.Snd (process_t s_pot_l t1)
     | S.Hd t1 -> S.Hd (process_t s_pot_l t1)
     | S.Tl t1 -> S.Tl (process_t s_pot_l t1)
     | S.Cons (t1, t2, t3) -> S.Cons (process_t s_pot_l t1, process_t s_pot_l t2, process_t s_pot_l t3)
     | S.Node (t1, t2, t3, t4) -> S.Node (process_t s_pot_l t1, process_t s_pot_l t2, process_t s_pot_l t3, process_t s_pot_l t4)
     | S.Ref (t1, t2) -> S.Ref (process_t s_pot_l t1, process_t s_pot_l t2)
     | S.Assign (t1, t2) -> S.Assign (process_t s_pot_l t1, process_t s_pot_l t2)
     | S.Deref t1 -> S.Deref (process_t s_pot_l t1)
     | S.Aliasrgn (t1, t2) -> S.Aliasrgn (process_t s_pot_l t1, process_t s_pot_l t2)
     | S.Freergn t1 -> S.Freergn (process_t s_pot_l t1)
     | S.Sequence (t1, t2) -> S.Sequence (process_t s_pot_l t1, process_t s_pot_l t2)
     | _ -> te)
    mty alpha_l rgn_l

let process t = process_t StrMap.empty t
