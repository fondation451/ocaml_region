open Util

module S = Ast

let rgn_of t =
  match S.get_type t with
  |S.THnd(r) -> r
  |_ -> assert false

let grow_ls ls =
  match ls with
  | None -> None
  | Some i -> Some (i+1)

let shrink_ls ls =
  match ls with
  | None -> None
  | Some i -> Some(i-1)

let add_ls ls ls' =
  match ls, ls' with
  | Some i, Some i' -> Some (i+i')
  | Some i, _ -> Some i
  | _ -> ls'

let max_ls ls ls' =
  match ls, ls' with
  | Some i, Some i' -> Some (max i i')
  | Some i, _ -> Some i
  | _ -> ls'

let rec sized_type_returned mty =
  match mty with
  | S.TFun (mty_l, mty2, _) -> (List.exists sized_type_returned mty_l) || sized_type_returned mty2
  | S.TCouple (mty1, mty2, _) -> (sized_type_returned mty1) || (sized_type_returned mty2)
  | S.TRef (_, mty1, _) -> sized_type_returned mty1
  | S.TList (_, _, _) -> true
  | S.TTree (_, _, _, _) -> true
  | _ -> false

let rec merge_mty mty_out mty_ls =
  match mty_out, mty_ls with
  | S.TFun (mty_l, mty2, r), S.TFun (mty_l', mty2', _) ->
    S.TFun (List.map2 merge_mty mty_l mty_l', merge_mty mty2 mty2', r)
  | S.TCouple (mty1, mty2, r), S.TCouple (mty1', mty2', _) ->
    S.TCouple (merge_mty mty1 mty1', merge_mty mty2 mty2', r)
  | S.TList (_, mty1, r), S.TList (ls, mty1', _) ->
    S.TList (ls, merge_mty mty1 mty1', r)
  | S.TTree (_, _, mty1, r), S.TTree (lsn, lsd, mty1', _) ->
    S.TTree (lsn, lsd, merge_mty mty1 mty1', r)
  | S.TRef (_, mty1, r), S.TRef (id, mty1', _) ->
    S.TRef (id, merge_mty mty1 mty1', r)
  |_ -> mty_out

let ref_env = Hashtbl.create 10

let rec process_ls env_f env t =
  Printf.printf "--------- LS PROCCES ------------\n%s\n\n" (S.show_typed_term t);
  let te = S.get_term t in
  let mty = S.get_type t in
  let alpha_l = S.get_alpha_l t in
  let rgn_l = S.get_rgn_l t in
  let (te', mty') =
    match te with
    | S.Var var -> S.Var var, StrMap.find var env
    | S.Unit -> S.Unit, mty
    | S.Bool b -> S.Bool b, mty
    | S.Int i -> S.Int i, mty
    | S.Binop (op, t1, t2) ->
      let t1' = process_ls env_f env t1 in
      S.Binop (op, t1', process_ls env_f env t2), S.get_type t1'
    | S.Not t1 ->
      let t1' = process_ls env_f env t1 in
      S.Not t1', S.get_type t1'
    | S.Neg t1 ->
      let t1' = process_ls env_f env t1 in
      S.Neg t1', S.get_type t1'
    | S.Comp (c, t1, t2) ->
      let t1' = process_ls env_f env t1 in
      S.Comp (c, t1', process_ls env_f env t2), S.get_type t1'
    | S.Fun (f, x_l, t1, t2, pot) -> te, mty
      (* let env' =
        List.fold_left
          (fun out x -> StrMap.add x (lift_mty (find_var_mty t1 x)) out)
          env (f::x_l)
      in
      let t1' = process_ls env_f env' t1 in
      let t2' = process_ls env_f env t2 in
      let mty1 = S.get_type t1' in
      let r = rgn_of t2' in
      S.Fun(f, x_l, t1', t2', pot),
      S.SFun(List.map (fun x -> StrMap.find x env') x_l, mty1, r) *)
    | S.App (t1, arg_l_app) -> begin
      let t1' = process_ls env_f env t1 in
      let t2_l' =
        List.fold_right
          (fun x t2_l' -> (process_ls env_f env (S.mk_term (S.Var x) (StrMap.find x env) [] []))::t2_l')
          arg_l_app []
      in
      if sized_type_returned (S.get_type t1') then
        let (arg_l, t_fun) =
          match S.get_term t1' with
          | S.Var v -> StrMap.find v env_f
          | S.Fun (f, arg_l, t_fun, _, _) -> (arg_l, t_fun)
        in
        let tmp =
          List.fold_right2
            (fun x t2 out ->
              S.mk_term
                (S.Let (x, t2, out))
                (S.get_type out)
                (S.get_alpha_l out)
                (S.get_rgn_l out))
            arg_l t2_l' t_fun
        in
        Printf.printf "OKK CA VA \n";
        S.App (t1', arg_l_app), merge_mty mty (S.get_type (process_ls env_f env tmp))
      else
      (Printf.printf "NUL !!!\n";
        S.App (t1', arg_l_app), mty)
    end
    | S.If (t1, t2, t3) ->
      let t3' = process_ls env_f env t3 in
      S.If (process_ls env_f env t1, process_ls env_f env t2, t3'), S.get_type t3'
    | S.MatchList (var_match, t_nil, x, xs, t_cons) -> begin
      let (S.TList (ls, mty_x, r)) = StrMap.find var_match env in
      match ls with
      | Some i when i = 0 ->
        let t_nil' = process_ls env_f env t_nil in
        S.MatchList (var_match, t_nil', x, xs, t_cons), S.get_type t_nil'
      | _ ->
        let env =
          StrMap.add x mty_x
            (StrMap.add xs (S.TList (shrink_ls ls, mty_x, r)) env)
        in
        let t_cons' = process_ls env_f env t_cons in
        S.MatchList (var_match, t_nil, x, xs, t_cons'), S.get_type t_cons'
    end
    | S.MatchTree (var_match, t_leaf, x, tl, tr, t_node) -> begin
      let (S.TTree (lsn, lsd, mty_x, r)) = StrMap.find var_match env in
      match lsn with
      | Some i when i = 0 ->
        let t_leaf' = process_ls env_f env t_leaf in
        S.MatchTree (var_match, t_leaf', x, tl, tr, t_node), S.get_type t_leaf'
      |_ ->
        let env =
          StrMap.add x mty_x
            (StrMap.add
              tl
              (S.TTree (shrink_ls lsn, shrink_ls lsd, mty_x, r))
              (StrMap.add
                tr
                (S.TTree (shrink_ls lsn, shrink_ls lsd, mty_x, r))
                env))
        in
        let t_node' = process_ls env_f env t_node in
        S.MatchTree (var_match, t_leaf, x, tl, tr, t_node'), S.get_type t_node'
    end
    | S.Let (x, t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let env = StrMap.add x (S.get_type t1') env in
      let t2' = process_ls env_f env t2 in
      S.Let (x, t1', t2'), S.get_type t2'
    | S.Letrec (f, t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let env = StrMap.add f (S.get_type t1') env in
      let (S.Fun (f, arg_l, t_fun, _, _)) = S.get_term t1' in
      let env_f = StrMap.add f (arg_l, t_fun) env_f in
      let t2' = process_ls env_f env t2 in
      S.Letrec (f, t1', t2'), S.get_type t2'
    | S.Pair (t1, t2, t3) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let t3' = process_ls env_f env t3 in
      let mty1 = S.get_type t1' in
      let mty2 = S.get_type t2' in
      let r = rgn_of t3' in
      S.Pair (t1', t2', t3'), S.TCouple (mty1, mty2, r)
    | S.Fst t1 ->
      let t1' = process_ls env_f env t1 in
      let (S.TCouple (mty', _, _)) = S.get_type t1' in
      S.Fst t1', mty'
    | S.Snd t1 ->
      let t1' = process_ls env_f env t1 in
      let (S.TCouple (_, mty', _)) = S.get_type t1' in
      S.Snd t1', mty'
    | S.Hd t1 ->
      let t1' = process_ls env_f env t1 in
      let (S.TList (_, mty', _)) = S.get_type t1' in
      S.Hd t1', mty'
    | S.Tl t1 ->
      let t1' = process_ls env_f env t1 in
      let (S.TList (ls, mty1, r)) = S.get_type t1' in
      S.Tl t1', S.TList (shrink_ls ls, mty1, r)
    | S.Nil ->
      let (S.TList (_, mty1, r)) = mty in
      S.Nil, S.TList (Some 0, mty1, r)
    | S.Leaf ->
      let (S.TTree (_, _, mty1, r)) = mty in
      S.Leaf, S.TTree (Some 0, Some 0, mty1, r)
    | S.Cons (t1, t2, t3) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let t3' = process_ls env_f env t3 in
      let mty1 = S.get_type t1' in
      let (S.TList (ls, _, _)) = S.get_type t2' in
      let r = rgn_of t3' in
      S.Cons (t1', t2', t3'), S.TList (grow_ls ls, mty1, r)
    | S.Node (t1, t2, t3, t4) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let t3' = process_ls env_f env t3 in
      let t4' = process_ls env_f env t4 in
      let mty1 = S.get_type t1' in
      let (S.TTree (ls1, ls2, _, _)) = S.get_type t2' in
      let (S.TTree (ls1', ls2', _, _)) = S.get_type t3' in
      let r = rgn_of t4' in
      S.Node (t1', t2', t3', t4'), S.TTree (grow_ls (add_ls ls1 ls1'), grow_ls (max_ls ls2 ls2'), mty1, r)
    | S.Ref (t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let mty1 = S.get_type t1' in
      let r = rgn_of t2' in
      let id = mk_id () in
      Hashtbl.replace ref_env id mty1;
      S.Ref (t1', t2'), S.TRef (id, mty1, r)
    | S.Assign (t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let (S.TRef (id, _, _)) = S.get_type t1' in
      Hashtbl.replace ref_env id (S.get_type t2');
      Printf.printf "HASH SABLE REF\n";
      Hashtbl.iter (fun id mty -> Printf.printf "%d : %s\n" id (S.show_rcaml_type mty)) ref_env;
      S.Assign (t1', t2'), S.TUnit
    | S.Deref t1 ->
      let t1' = process_ls env_f env t1 in
      let (S.TRef (id, _, _)) = S.get_type t1' in
      Printf.printf "HASH SABLE REF\n";
      Hashtbl.iter (fun id mty -> Printf.printf "%d : %s\n" id (S.show_rcaml_type mty)) ref_env;
      S.Deref t1', Hashtbl.find ref_env id
    | S.Newrgn -> S.Newrgn, mty
    | S.Aliasrgn (t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      S.Aliasrgn (t1', t2'), S.get_type t2'
    | S.Freergn t1 -> S.Freergn (process_ls env_f env t1), S.TUnit
    | S.Sequence (t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      S.Sequence (t1', t2'), S.get_type t2'
  in
  S.mk_term te' (merge_mty mty mty') alpha_l rgn_l

let process t =
  let t' = process_ls StrMap.empty StrMap.empty t in
  t'
