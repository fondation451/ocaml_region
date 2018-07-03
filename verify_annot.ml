open Util

module S = Simpl

let rgn_of r = r

let show_out out =
  StrMap.fold (fun k pot out -> Printf.sprintf "%s%s : %s\n" out k (Lit.show pot)) out ""

let rec remove_p = function
  | Lit.Var _ -> Lit.Lit 0
  | Lit.Add p_l -> Lit.Add (List.map remove_p p_l)
  | Lit.Mul p_l -> Lit.Mul (List.map remove_p p_l)
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

let rec pot_of env t =
  match S.get_term t with
  | S.Var v -> begin
    Printf.printf "DEBUG2 %s\n" v;
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

let rec instanciate pot arg_l =
  let subs i = List.nth arg_l i in
  match pot with
  | S.PPot id -> Lit.Var id
  | S.PLit i ->  Lit.Lit i
  | S.PSize i | S.PLen i | S.PNode i | S.PDepth i -> Lit.Var (subs i)
  | S.PAdd (p1, p2) -> Lit.Add [instanciate p1 arg_l ; instanciate p2 arg_l]
  | S.PMin p1 -> Lit.Mul [Lit.Lit (-1) ; instanciate p1 arg_l]
  | S.PMul (p1, p2) -> Lit.Mul [instanciate p1 arg_l ; instanciate p2 arg_l]
  | S.PUnit -> Lit.Unit

let add_to_env x mty env =
  let add_ls x = function
    | Some i -> StrMap.add x (Lit.Lit i) env
    | None -> StrMap.add x (Lit.Var (mk_var ())) env
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
            StrMap.add r (try Lit.Add [StrMap.find r out_p ; pot'] with Not_found -> pot') out_p)
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
        let pot_r = try StrMap.find r out_p with Not_found -> Lit.Unit in
        StrMap.add r (Lit.Add [pot_r ; Lit.Lit (cost_of RPAIR)]) out_p)
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
        let pot_r = try StrMap.find r out_p with Not_found -> Lit.Unit in
        StrMap.add r (Lit.Add [pot_r ; Lit.Lit (cost_of RCONS)]) out_p)
      out
  | S.Leaf -> out
  | S.Node (t1, t2, t3, t4) ->
    let S.TTree(_, _, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t t4 env s_pot_l (verify_t t3 env s_pot_l (verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out))) in
    List.map
      (fun out_p ->
        let pot_r = try StrMap.find r out_p with Not_found -> Lit.Unit in
        StrMap.add r (Lit.Add [pot_r ; Lit.Lit (cost_of RNODE)]) out_p)
      out
  | S.Ref (t1, t2) ->
    let S.TRef(_, _, r) = mty in
    let r = rgn_of r in
    let out = verify_t t2 env s_pot_l (verify_t t1 env s_pot_l out) in
    List.map
      (fun out_p ->
        let pot_r = try StrMap.find r out_p with Not_found -> Lit.Unit in
        StrMap.add r (Lit.Add [pot_r ; Lit.Lit (cost_of RREF)]) out_p)
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
  let env = List.fold_left (fun env x -> StrMap.add x (Lit.Var x) env) StrMap.empty arg_l in
  let env, _ = pot_of env t in
  Printf.printf "ENV : %s\n" (strmap_str env Lit.show);
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
              Lit.Add [pot ; Lit.Mul [Lit.Lit (-1) ; pot_p]]
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
