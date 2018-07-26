open Util

module S = Ast

exception Solved of Lit.t StrMap.t

let rec merge_mty mty mty' =
  match mty, mty' with
  | S.TFun (mty_l, mty2, r), S.TFun (mty_l', mty2', _) -> S.TFun (List.map2 merge_mty mty_l mty_l', merge_mty mty2 mty2', r)
  | S.TCouple (mty1, mty2, r), S.TCouple (mty1', mty2', _) -> S.TCouple (merge_mty mty1 mty1', merge_mty mty2 mty2', r)
  | S.TList (_, mty1, r), S.TList (ls, mty1', _) -> S.TList (Maxima.canonic ls, merge_mty mty1 mty1', r)
  | S.TTree (_, _, mty1, r), S.TTree (lsn, lsd, mty1', _) -> S.TTree (Maxima.canonic lsn, Maxima.canonic lsd, merge_mty mty1 mty1', r)
  | S.TRef (id, mty1, r), S.TRef (_, mty1', _) -> S.TRef (id, merge_mty mty1 mty1', r)
  | S.TAlpha a, _ -> mty'
  | _ -> mty

let rec minus_mty mty mty' =
  match mty, mty' with
  | S.TFun (mty_l, mty2, r), S.TFun (mty_l', mty2', _) -> S.TFun (List.map2 minus_mty mty_l mty_l', minus_mty mty2 mty2', r)
  | S.TCouple (mty1, mty2, r), S.TCouple (mty1', mty2', _) -> S.TCouple (minus_mty mty1 mty1', minus_mty mty2 mty2', r)
  | S.TList (ls, mty1, r), S.TList (ls', mty1', _) -> S.TList (Lit.sub ls ls', minus_mty mty1 mty1', r)
  | S.TTree (lsn, lsd, mty1, r), S.TTree (lsn', lsd', mty1', _) ->
    S.TTree (Lit.sub lsn lsn', Lit.sub lsd lsd', minus_mty mty1 mty1', r)
  | S.TRef (id, mty1, r), S.TRef (_, mty1', _) -> S.TRef (id, minus_mty mty1 mty1', r)
  | S.TAlpha a, _ -> mty'
  | _ -> mty

let rec op_mty f mty mty' =
  match mty, mty' with
  | S.TFun (mty_l, mty2, r), S.TFun (mty_l', mty2', _) -> S.TFun (List.map2 (op_mty f) mty_l mty_l', op_mty f mty2 mty2', r)
  | S.TCouple (mty1, mty2, r), S.TCouple (mty1', mty2', _) -> S.TCouple (op_mty f mty1 mty1', op_mty f mty2 mty2', r)
  | S.TList (ls, mty1, r), S.TList (ls', mty1', _) -> S.TList (f ls ls', op_mty f mty1 mty1', r)
  | S.TTree (lsn, lsd, mty1, r), S.TTree (lsn', lsd', mty1', _) -> S.TTree (f lsn lsn', f lsd lsd', op_mty f mty1 mty1', r)
  | S.TRef (id, mty1, r), S.TRef (_, mty1', _) -> S.TRef (id, op_mty f mty1 mty1', r)
  | S.TAlpha a, _ -> mty'
  | _ -> mty

let add_i_to_sub x i s =
  if not (StrMap.mem x s) || (StrMap.find x s = Lit.lit i) then
    StrMap.add x (Lit.lit i) s
  else
    raise (S.Ls_Infer_Error "")

let add_to_sub ls ls' env =
  Printf.printf "ADD_TO_SUB %s : %s\n\n" (Lit.show ls) (Lit.show ls');
  match ls with
  | Lit.Var x -> StrMap.add x ls' env
  | _ -> assert false

let rec mk_sub mty mty' out =
  let union s s' = StrMap.union (fun _ _ _ -> assert false) s s' in
  match mty, mty' with
  | S.TFun (mty_l, mty2, _), S.TFun (mty_l', mty2', _) ->
  List.fold_left2 (fun out mty1 mty1' -> mk_sub mty1 mty1' out) (mk_sub mty2 mty2' out) mty_l mty_l'
  | S.TCouple (mty1, mty2, _), S.TCouple (mty1', mty2', _) -> mk_sub mty2 mty2' (mk_sub mty1 mty1' out)
  | S.TList (ls, mty1, _), S.TList (ls', mty1', _) -> mk_sub mty1 mty1' (add_to_sub ls ls' out)
  | S.TTree (lsn, lsd, mty1, _), S.TTree (lsn', lsd', mty1', _) ->
    mk_sub mty1 mty1' (add_to_sub lsn lsn' (add_to_sub lsd lsd' out))
  | S.TRef (_, mty1, _), S.TRef (_, mty1', _) -> mk_sub mty1 mty1' out
  | _ -> out

let ls_of mty =
  let rec loop mty out =
    match mty with
    | S.TFun (mty_l, mty2, r) -> List.fold_left (fun out mty1 -> loop mty1 out) (loop mty2 out) mty_l
    | S.TCouple (mty1, mty2, r) -> loop mty2 (loop mty1 out)
    | S.TList (ls, mty1, r) -> loop mty1 (ls::out)
    | S.TTree (lsn, lsd, mty1, r) -> loop mty1 (lsn::lsd::out)
    | S.TRef (id, mty1, r) -> loop mty1 out
    | _ -> out
  in loop mty []

let fv mty = List.fold_left (fun out lit -> StrSet.union (Lit.fv lit) out) StrSet.empty (ls_of mty)
(*
  let rec loop mty out =
    match mty with
    | S.TFun (mty_l, mty2, r) -> List.fold_left (fun out mty1 -> loop mty1 out) (loop mty2 out) mty_l
    | S.TCouple (mty1, mty2, r) -> loop mty2 (loop mty1 out)
    | S.TList (ls, mty1, r) -> loop mty1 (StrSet.union (Lit.fv ls) out)
    | S.TTree (lsn, lsd, mty1, r) -> loop mty1 (StrSet.union (Lit.fv lsn) (StrSet.union (Lit.fv lsd) out))
    | S.TRef (id, mty1, r) -> loop mty1 out
    | _ -> out
  in loop mty StrSet.empty
*)
let apply s mty =
  let rec loop mty =
    match mty with
    | S.TFun (mty_l, mty2, r) -> S.TFun (List.map loop mty_l, loop mty2, r)
    | S.TCouple (mty1, mty2, r) -> S.TCouple (loop mty1, loop mty2, r)
    | S.TList (ls, mty1, r) -> S.TList (Lit.apply s ls, loop mty1, r)
    | S.TTree (lsn, lsd, mty1, r) -> S.TTree (Lit.apply s lsn, Lit.apply s lsd, loop mty1, r)
    | S.TRef (id, mty1, r) -> S.TRef (id, loop mty1, r)
    | _ -> mty
  in loop mty

let instanciate mty lit =
  let l_lit = StrSet.elements lit in
  let l_v = ref StrSet.empty in
  let new_v () =
    let v = mk_var () in
    l_v := StrSet.add v (!l_v);
    Lit.var v
  in
  let new_lit () =
    let rec loop l_lit out =
      match l_lit with
      | [] -> Maxima.canonic (Lit.add (new_v ()) out)
      | lit::l_lit' -> loop l_lit' (Lit.add (Lit.mul (Lit.var lit) (new_v ())) out)
    in loop l_lit (Lit.lit 0)
  in
  let rec loop mty =
    match mty with
    | S.TFun (mty_l, mty2, r) -> S.TFun(List.map loop mty_l, loop mty2, r)
    | S.TCouple (mty1, mty2, r) -> S.TCouple (loop mty1, loop mty2, r)
    | S.TList (_, mty1, r) -> S.TList (new_lit (), loop mty1, r)
    | S.TTree (_, _, mty1, r) -> S.TTree (new_lit (), new_lit (), loop mty1, r)
    | S.TRef (id, mty1, r) -> S.TRef (id, loop mty1, r)
    | _ -> mty
  in (loop mty, !l_v)

let sub_union s1 s2 = StrMap.union (fun _ l1 l2 -> Some l1) s1 s2

let cost_of_sol sol = StrMap.fold (fun _ l out -> Lit.cost_of l + out) sol 0

let resolve lit_nul coef =
  Printf.printf "{\n%s\n}\n\n" (strset_str coef);
  let cv l = StrSet.elements (StrSet.inter (Lit.fv l) coef) in
  let solve sol (c, l) = StrMap.add c (Maxima.solve l c) sol in
  let solve_l lit_nul sol = List.fold_left solve sol lit_nul in
  let separate_lit lit_nul =
    List.fold_left
      (fun (out_solve, out_nul) l ->
        match cv l with
        | [c] -> (c, l)::out_solve, out_nul
        | _ -> out_solve, l::out_nul)
      ([], []) lit_nul
  in
  let rec loop lit_nul sol =
    let lit_nul = List.map (fun l -> Maxima.canonic (Lit.apply sol l)) lit_nul in
    let lit_nul = List.filter (fun l -> match l with | Lit.Lit n -> false | _ -> true) lit_nul in
  Printf.printf "RESOlVE CURRENT LIT NUl :\n";
  List.iter (fun l -> Printf.printf "{\n%s\n}\n" (Lit.show l)) lit_nul;
  Printf.printf "RESOlVE CURRENT SOL :\n%s\n" (strmap_str sol Lit.show);
  print_newline ();
    let (lit_nul_to_solve, lit_nul') = separate_lit lit_nul in
    let sol' = solve_l lit_nul_to_solve sol in
    if lit_nul' = [] then
      sol'
    else if List.length lit_nul = List.length lit_nul' then
      try begin
        let sol_l =
          List.fold_left
            (fun out l ->
              let c_l = cv l in
              List.rev_append
                (List.fold_left
                  (fun out c ->
                    let sol' = List.fold_left (fun sol' c' -> if c' <> c then StrMap.add c' (Lit.lit 0) sol' else sol') sol' c_l in
                    let sol' = loop lit_nul' sol' in
                    if cost_of_sol sol' = 0 && StrMap.cardinal sol' = StrSet.cardinal coef then
                      raise (Solved sol')
                    else
                      sol'::out)
                  out c_l)
                out)
            [] lit_nul'
        in
        let sol_l = List.filter (fun sol -> StrMap.cardinal sol = StrSet.cardinal coef) sol_l in
        try
          list_min (fun sol sol' -> compare (cost_of_sol sol) (cost_of_sol sol')) sol_l
        with Invalid_argument _ -> sol'
      end with Solved sol -> sol
    else
      loop lit_nul' sol'
  in loop (List.map Maxima.canonic lit_nul) StrMap.empty

let rec infer f arg_l f_mty env t =
  print_newline ();
  let te = S.get_term t in
  let mty = S.get_type t in
  let merge mty_l' = List.map (fun (s, m) -> s, merge_mty mty m) mty_l' in
  let mk te mty = S.mk_term te mty (S.get_alpha_l t) (S.get_rgn_l t) in
  let rec infer_t env t (* : (Lit.t Util.StrMap.t * S.rcaml_type) list*)=
    Printf.printf "--------- LS INFER ------------\n%s\n\n" (S.show_typed_term t);
    Printf.printf "ENV : %s\n\n" (strmap_str env S.show_rcaml_type);
    let te = S.get_term t in
    let mty = S.get_type t in
    let merge mty' = merge_mty mty mty' in
    match te with
    | S.Var v -> [(StrMap.empty, StrMap.find v env)]
    | S.Binop (op, t1, t2) -> [StrMap.empty, mty]
    | S.Not t1 -> [StrMap.empty, mty]
    | S.Neg t1 -> [StrMap.empty, mty]
    | S.Comp (op, t1, t2) -> [StrMap.empty, mty]
    | S.Fun (s, arg_l, t1, t2, _) ->
      let mty_arg, mty_out = infer s arg_l mty env t1 in
      let S.THnd r = S.get_type t2 in
      [StrMap.empty, S.TFun (mty_arg, mty_out, r)]
    | S.App (t1, arg_l) ->
      let S.TFun (f_mty_l, f_mty2, _) = snd (List.hd (infer_t env t1)) in (* TODO *)
      let mty_arg_l = List.map (fun x -> StrMap.find x env) arg_l in
      let fv_mty_l = StrSet.elements (List.fold_left (fun out f_mty1 -> StrSet.union (fv f_mty1) out) StrSet.empty f_mty_l) in
      let sub_arg = List.fold_left2 (fun out mty_f mty_arg -> mk_sub mty_f mty_arg out) StrMap.empty f_mty_l mty_arg_l in
      Printf.printf "SUB_ARG : %s\n" (strmap_str sub_arg Lit.show); print_newline ();
      let mty' = apply sub_arg f_mty2 in
(*      merge [StrMap.empty, mty']*)
     [StrMap.empty, mty']
    | S.If (t1, t2, t3) ->
      let mty2 = infer_t env t2 in
      let mty3 = infer_t env t3 in
(*      let mty_out =
        List.fold_left
          (fun out (s2, m2) ->
            List.fold_left
              (fun out (s3, m3) -> (sub_union s2 s3, (op_mty Lit.add m2 m3))::out)
              out mty3)
          [] mty2
      in
      mty_out*)
      List.rev_append mty2 mty3
    | S.MatchList (l, t_nil, x, xs, t_cons) ->
      let S.TList (l_ls, mty_x, r) = StrMap.find l env in
      let mty_nil = infer_t env t_nil in
      let env = StrMap.add x mty_x (StrMap.add xs (S.TList (Lit.add l_ls (Lit.lit (-1)), mty_x, r)) env) in
      let mty_cons = infer_t env t_cons in
      let mty_match =
        match l_ls with
        | Lit.Lit i -> if i = 0 then mty_nil else mty_cons
        | Lit.Var v -> List.rev_append (List.map (fun (sub, mty) -> StrMap.add v (Lit.lit 0) sub, mty) mty_nil) mty_cons
        | _ -> assert false
      in
      mty_match
    | S.MatchTree (t, t_leaf, x, tl, tr, t_node) ->
      let S.TTree (lsn, lsd, mty_x, r) = StrMap.find t env in
      let mty_leaf = infer_t env t_leaf in
      let env1 =
        StrMap.add x mty_x
          (StrMap.add tl (S.TTree (Lit.div (Lit.add lsn (Lit.lit (-1))) (Lit.lit 2), Lit.lit 0, mty_x, r))
            (StrMap.add tr (S.TTree (Lit.div (Lit.add lsn (Lit.lit (-1))) (Lit.lit 2), Lit.lit 0, mty_x, r)) env))
      in
      let env2 =
        StrMap.add x mty_x
          (StrMap.add tl (S.TTree (Lit.lit 0, Lit.add lsd (Lit.lit (-1)), mty_x, r))
            (StrMap.add tr (S.TTree (Lit.lit 0, Lit.add lsd (Lit.lit (-1)), mty_x, r)) env))
      in
      let env =
        StrMap.add x mty_x
          (StrMap.add tl (S.TTree (Lit.div (Lit.add lsn (Lit.lit (-1))) (Lit.lit 2), Lit.add lsd (Lit.lit (-1)), mty_x, r))
            (StrMap.add tr (S.TTree (Lit.div (Lit.add lsn (Lit.lit (-1))) (Lit.lit 2), Lit.add lsd (Lit.lit (-1)), mty_x, r)) env))
      in
      let mty_node = infer_t env t_node in
      let mty_node1 = infer_t env1 t_node in
      let mty_node2 = infer_t env2 t_node in
      let mty_match =
        match lsn, lsd with
        | Lit.Lit i, Lit.Lit i' -> if i = 0 then mty_leaf else List.rev_append mty_node1 mty_node2
        | Lit.Var v, Lit.Var v' ->
          List.rev_append
            (List.map
              (fun (sub, mty) -> StrMap.add v (Lit.lit 0) (StrMap.add v' (Lit.lit 0) sub), mty)
              mty_leaf)
            mty_node
(*            (List.rev_append mty_node1 mty_node2) *)
(*            (List.rev_append
              (List.map (fun (sub, mty) -> StrMap.add v (Lit.Lit 0) sub, mty) mty_node2)
              (List.map (fun (sub, mty) -> StrMap.add v' (Lit.Lit 0) sub, mty) mty_node1))*)
        | _ -> assert false
      in
      mty_match
    | S.Let (x, t1, t2) | S.Letrec (x, t1, t2) ->
      let mty1 = infer_t env t1 in
      let mty_x = snd (List.hd mty1) in
      let env = StrMap.add x mty_x env in
      let mty2 = infer_t env t2 in
      mty2
    | S.Pair (t1, t2, t3) ->
      let mty1 = infer_t env t1 in
      let mty2 = infer_t env t2 in
      let S.THnd r = S.get_type t3 in
      let mty_out =
        List.fold_left
          (fun out (s1, m1) -> List.fold_left
              (fun out (s2, m2) -> (sub_union s1 s2, S.TCouple (m1, m2, r))::out)
              out mty2)
          [] mty1
      in
      mty_out
    | S.Fst t1 ->
      let mty1 = infer_t env t1 in
      let mty_out = List.map (fun (s1, m1) -> let S.TCouple (m_out, _, _) = m1 in s1, m_out) mty1 in
      mty_out
    | S.Snd t1 ->
      let mty1 = infer_t env t1 in
      let mty_out = List.map (fun (s1, m1) -> let S.TCouple (_, m_out, _) = m1 in s1, m_out) mty1 in
      mty_out
    | S.Hd t1 ->
      let mty1 = infer_t env t1 in
      let mty_out = List.map (fun (s1, m1) -> let S.TList (_, m_out, _) = m1 in s1, m_out) mty1 in
      mty_out
    | S.Tl t1 ->
      let mty1 = infer_t env t1 in
      let mty_out =
        List.map
          (fun (s1, m1) ->
            let S.TList (ls, m_out, r) = m1 in
            s1, S.TList (Lit.add ls (Lit.lit (-1)), m_out, r))
          mty1
      in
      mty_out
    | S.Nil ->
      let S.TList (_, mty1, r) = mty in
      [StrMap.empty, S.TList (Lit.lit 0, mty1, r)]
    | S.Cons (t1, t2, t3) ->
      let mty1 = infer_t env t1 in
      let mty2 = infer_t env t2 in
      let S.THnd r = S.get_type t3 in
      let mty_out =
        List.fold_left
          (fun out (s1, m1) -> List.fold_left
              (fun out (s2, m2) ->
                let S.TList (ls, _, _) = m2 in
                (sub_union s1 s2, S.TList (Lit.add ls (Lit.lit 1), m1, r))::out)
              out mty2)
          [] mty1
      in
      mty_out
    | S.Leaf ->
      let S.TTree (_, _, mty1, r) = mty in
      [StrMap.empty, S.TTree (Lit.lit 0, Lit.lit 0, mty1, r)]
    | S.Node (t1, t2, t3, t4) ->
      let mty1 = infer_t env t1 in
      let mty2 = infer_t env t2 in
      let mty3 = infer_t env t3 in
      let S.THnd r = S.get_type t4 in
      let mty_out =
        List.fold_left
          (fun out (s1, m1) -> List.fold_left
            (fun out (s2, m2) -> List.fold_left
              (fun out (s3, m3) ->
                let S.TTree (lsn, lsd, _, _) = m2 in
                let S.TTree (lsn', lsd', _, _) = m3 in
                let s = sub_union s1 (sub_union s2 s3) in
                (s, S.TTree (Lit.add (Lit.lit 1) (Lit.add lsn lsn'), Lit.add lsd (Lit.lit 1), m1, r))::
                (s, S.TTree (Lit.add (Lit.lit 1) (Lit.add lsn lsn'), Lit.add lsd' (Lit.lit 1), m1, r))::
                out)
              out mty3)
            out mty2)
          [] mty1
      in
      mty_out
    | S.Ref (t1, t2) -> assert false
    | S.Assign (t1, t2) -> assert false
    | S.Deref t1 -> assert false
    | S.Aliasrgn (t1, t2) ->
      let mty2 = infer_t env t2 in
      mty2
    | S.Freergn t1 -> [StrMap.empty, mty]
    | S.Sequence (t1, t2) ->
      let mty2 = infer_t env t2 in
      mty2
    | _ -> [StrMap.empty, mty]
  in
  let S.TFun (mty_arg_l, mty_out, r) = f_mty in
  let mty_inst_l = List.map (fun m -> instanciate m StrSet.empty) mty_arg_l in
  let (mty_inst_l, fv_lit_l) = List.split mty_inst_l in
  let fv_lit = List.fold_left (fun out fv_lit -> StrSet.union fv_lit out) StrSet.empty fv_lit_l in
  Printf.printf "{\n%s\n}\n\n" (strset_str fv_lit);
  let (mty_out, fv_coef) = instanciate mty_out fv_lit in
  Printf.printf "{\n%s\n}\n\n" (strset_str fv_coef);
  let env =
    List.fold_left2
      (fun out arg mty_arg -> StrMap.add arg mty_arg out)
      (StrMap.add f (S.TFun (mty_inst_l, mty_out, r)) env)
      arg_l mty_inst_l
  in
  let mty_infered = infer_t env t in
  Printf.printf "MTY OUT : \n%s\n\n" (S.show_rcaml_type mty_out);
  Printf.printf "MTY INFERED :\n";
  List.iter (fun (s, m) -> Printf.printf "{\n%s\n%s\n}\n" (strmap_str s Lit.show) (S.show_rcaml_type m)) mty_infered;
  let mty_dif = List.map (fun (s, m) -> apply s (minus_mty mty_out m)) mty_infered in
  Printf.printf "MTY DIF :\n";
  List.iter (fun m -> Printf.printf "{\n%s\n}\n" (S.show_rcaml_type m)) mty_dif;
  let lit_nul = List.map Maxima.canonic (List.fold_left (fun out m -> List.rev_append (ls_of m) out) [] mty_dif) in
  Printf.printf "LIT NUL :\n";
  List.iter (fun l -> Printf.printf "{\n%s\n}\n" (Lit.show l)) lit_nul;
(*  let sub_dumb = List.fold_left (fun out va -> StrMap.add va (Lit.Lit 7) out) StrMap.empty fv_lit in
  let lit_nul = List.map (fun l -> Lit.canonic (Lit.apply sub_dumb l)) lit_nul in
  Printf.printf "LIT NUl INST :\n";
  List.iter (fun l -> Printf.printf "{\n%s\n}\n" (Lit.show l)) lit_nul;*)
  let sol = resolve lit_nul fv_coef in
  Printf.printf "SOL :\n%s\n" (strmap_str sol Lit.show);
  let mty_out = apply sol mty_out in
  Printf.printf "MTY OUT :\n%s\n\n" (S.show_rcaml_type mty_out);
(*  assert false;*)
(*  if f = "insert_tree" then assert false;
  if f = "to_tree" then assert false;*)
  mty_inst_l, mty_out
(*  if inf_const then begin
    let sol = resolve lit_nul true fv_lit in
    Printf.printf "SOL :\n%s\n" (strmap_str sol Lit.show);
    let mty_out = apply false sol mty_out in
    Printf.printf "MTY OUT :\n%s\n\n" (S.show_rcaml_type mty_out);
    if f = "insert_tree" then assert false;
    if f = "to_tree" then assert false;
    mty_arg_l, mty_out
  end else try
    let sol = resolve lit_nul false fv_lit in
    Printf.printf "SOL :\n%s\n" (strmap_str sol Lit.show);
    let mty_out = apply false sol mty_out in
    Printf.printf "MTY OUT :\n%s\n\n" (S.show_rcaml_type mty_out);
    if f = "to_tree" then assert false;
    mty_arg_l, mty_out
  with Lit.Bad_equation -> infer f arg_l f_mty env t*)

let rec process_t t env =
  Printf.printf "--------- LS PROCCES ------------\n%s\n\n" (S.show_typed_term t);
  Printf.printf "ENV : %s\n\n" (strmap_str env S.show_rcaml_type);
  print_newline ();
  let te = S.get_term t in
  let mty = S.get_type t in
  let merge mty' = merge_mty mty mty' in
  let mk te mty = S.mk_term te mty (S.get_alpha_l t) (S.get_rgn_l t) in
  match te with
  | S.Var v -> mk te (merge (StrMap.find v env))
  | S.Binop (op, t1, t2) -> mk (S.Binop (op, process_t t1 env, process_t t2 env)) mty
  | S.Not t1 -> mk (S.Not (process_t t1 env)) mty
  | S.Neg t1 -> mk (S.Neg (process_t t1 env)) mty
  | S.Comp (op, t1, t2) -> mk (S.Comp (op, process_t t1 env, process_t t2 env)) mty
  | S.Fun (s, arg_l, t1, t2, f_pot_l) ->
    let S.TFun (_, _, r) = mty in
    let mty_arg, mty_out = infer s arg_l mty env t1 in
    let mty' = S.TFun (mty_arg, mty_out, r) in
    let env = List.fold_left2 (fun out a m -> StrMap.add a m out) (StrMap.add s mty' env) arg_l mty_arg in
    mk (S.Fun (s, arg_l, process_t t1 env, process_t t2 env, f_pot_l)) (merge mty')
  | S.App (t1, arg_l) ->
    let t1' = process_t t1 env in
    let mty_arg_l = List.map (fun x -> StrMap.find x env) arg_l in
    let S.TFun (f_mty_arg_l, mty_out, _) = S.get_type t1' in
    let fv_mty_arg_l = StrSet.elements (List.fold_left (fun out mty1 -> StrSet.union (fv mty1) out) StrSet.empty f_mty_arg_l) in
    let sub_arg = List.fold_left2 (fun out f_mty_arg mty_arg -> mk_sub f_mty_arg mty_arg out) StrMap.empty f_mty_arg_l mty_arg_l in
    Printf.printf "SUB_ARG : %s\n" (strmap_str sub_arg Lit.show); print_newline ();
    let mty' = apply sub_arg mty_out in
    mk (S.App (t1', arg_l)) (merge mty')
  | S.If (t1, t2, t3) ->
    let t1' = process_t t1 env in
    let t2' = process_t t2 env in
    let t3' = process_t t3 env in
(*    let mty_if = max_mty (S.get_type t2') (S.get_type t3') in*)
    let mty_if = S.get_type t3' in
    mk (S.If (t1', t2', t3')) (merge mty_if)
  | S.MatchList (l, t_nil, x, xs, t_cons) ->
    let S.TList (l_ls, mty_x, r) = StrMap.find l env in
    let t_nil' = process_t t_nil env in
    let env = StrMap.add x mty_x (StrMap.add xs (S.TList (Lit.add l_ls (Lit.lit (-1)), mty_x, r)) env) in
    let t_cons' = process_t t_cons env in
    let mty_match =
      match l_ls with
      | Lit.Lit i -> if i = 0 then S.get_type t_nil' else S.get_type t_cons'
      | _ -> S.get_type t_cons'
    in
    mk (S.MatchList (l, t_nil', x, xs, t_cons')) (merge mty_match)
  | S.MatchTree (t, t_leaf, x, tl, tr, t_node) ->
    let S.TTree (lsn, lsd, mty_x, r) = StrMap.find t env in
    let t_leaf' = process_t t_leaf env in
    let env =
      StrMap.add x mty_x
        (StrMap.add tl (S.TTree (Lit.div (Lit.add lsn (Lit.lit (-1))) (Lit.lit 2), Lit.add lsd (Lit.lit (-1)), mty_x, r))
          (StrMap.add tr (S.TTree (Lit.div (Lit.add lsn (Lit.lit (-1))) (Lit.lit 2), Lit.add lsd (Lit.lit (-1)), mty_x, r)) env))
    in
    let t_node' = process_t t_node env in
    let mty_match =
      match lsn with
      | Lit.Lit i -> if i = 0 then S.get_type t_leaf' else S.get_type t_node'
      | _ -> S.get_type t_node'
    in
    mk (S.MatchTree (t, t_leaf', x, tl, tr, t_node')) (merge mty_match)
  | S.Let (x, t1, t2) ->
    let t1' = process_t t1 env in
    let env = StrMap.add x (S.get_type t1') env in
    let t2' = process_t t2 env in
    mk (S.Let (x, t1', t2')) (merge (S.get_type t2'))
  | S.Letrec (x, t1, t2) ->
    let t1' = process_t t1 env in
    let env = StrMap.add x (S.get_type t1') env in
    let t2' = process_t t2 env in
    mk (S.Letrec (x, t1', t2')) (merge (S.get_type t2'))
  | S.Pair (t1, t2, t3) ->
    let t1' = process_t t1 env in
    let t2' = process_t t2 env in
    let t3' = process_t t3 env in
    let S.THnd r = S.get_type t3' in
    mk (S.Pair (t1', t2', t3')) (merge (TCouple (S.get_type t1', S.get_type t2', r)))
  | S.Fst t1 ->
    let t1' = process_t t1 env in
    let S.TCouple (mty1, _, _) = S.get_type t1' in
    mk (S.Fst t1') (merge mty1)
  | S.Snd t1 ->
    let t1' = process_t t1 env in
    let S.TCouple (_, mty2, _) = S.get_type t1' in
    mk (S.Snd t1') (merge mty2)
  | S.Hd t1 ->
    let t1' = process_t t1 env in
    let S.TList (_, mty1, _) = S.get_type t1' in
    mk (S.Hd t1') (merge mty1)
  | S.Tl t1 ->
    let t1' = process_t t1 env in
    let S.TList (ls, mty1, r) = S.get_type t1' in
    mk (S.Tl t1') (merge (S.TList (Lit.add ls (Lit.lit (-1)), mty1, r)))
  | S.Nil ->
    let S.TList (_, mty1, r) = mty in
    mk S.Nil (merge (S.TList (Lit.lit 0, mty1, r)))
  | S.Cons (t1, t2, t3) ->
    let t1' = process_t t1 env in
    let t2' = process_t t2 env in
    let t3' = process_t t3 env in
    let mty1 = S.get_type t1' in
    let S.TList (ls, _, _) = S.get_type t2' in
    let S.THnd r = S.get_type t3' in
    mk (S.Cons (t1', t2', t3')) (merge (S.TList (Lit.add ls (Lit.lit 1), mty1, r)))
  | S.Leaf ->
    let S.TTree (_, _, mty1, r) = mty in
    mk S.Leaf (merge (S.TTree (Lit.lit 0, Lit.lit 0, mty1, r)))
  | S.Node (t1, t2, t3, t4) -> begin
    let t1' = process_t t1 env in
    let t2' = process_t t2 env in
    let t3' = process_t t3 env in
    let t4' = process_t t4 env in
    let mty1 = S.get_type t1' in
    let S.TTree (lsn1, lsd1, _, _) = S.get_type t2' in
    let S.TTree (lsn2, lsd2, _, _) = S.get_type t3' in
    let S.THnd r = S.get_type t4' in
    match lsd1, lsd2 with
    | Lit.Lit h1, Lit.Lit h2 ->
      let h = max h1 h2 in
      mk (S.Node (t1', t2', t3', t4')) (merge (S.TTree (Lit.add (Lit.lit 1) (Lit.add lsn1 lsn2), Lit.add (Lit.lit h) (Lit.lit 1), mty1, r)))
    | _ ->
      mk (S.Node (t1', t2', t3', t4')) (merge (S.TTree (Lit.add (Lit.lit 1) (Lit.add lsn1 lsn2), Lit.add lsd1 (Lit.lit 1), mty1, r)))
  end
  | S.Ref (t1, t2) -> assert false
  | S.Assign (t1, t2) -> assert false
  | S.Deref t1 -> assert false
  | S.Aliasrgn (t1, t2) ->
    let t1' = process_t t1 env in
    let t2' = process_t t2 env in
    mk (S.Aliasrgn (t1', t2')) (merge (S.get_type t2'))
  | S.Freergn t1 ->
    let t1' = process_t t1 env in
    mk (S.Freergn t1') mty
  | S.Sequence (t1, t2) ->
    let t1' = process_t t1 env in
    let t2' = process_t t2 env in
    mk (S.Sequence (t1', t2')) (merge (S.get_type t2'))
  | _ -> t


let process t = process_t t StrMap.empty
