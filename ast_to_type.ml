open Util

module S = Ast

(* ALGORITHM W *)

let str_of_subs s =
  let st, sr = s in
  Printf.sprintf "%s\n%s" (strmap_str st S.show_rcaml_type) (strmap_str sr S.show_regions)

let fv_mty mty =
  let rec loop mty out =
    match mty with
    | S.TAlpha a -> StrSet.add a out
    | S.TInt | S.TBool | S.TUnit | S.THnd(_) -> out
    | S.TFun (mty_l, mty2, _) -> List.fold_left (fun out mty -> loop mty out) (loop mty2 out) mty_l
    | S.TCouple (mty1, mty2, _) -> loop mty1 (loop mty2 out)
    | S.TList (_, mty1, _) -> loop mty1 out
    | S.TTree (_, _, mty1, _) -> loop mty1 out
    | S.TRef (_, mty1, _) -> loop mty1 out
  in loop mty StrSet.empty

let fv_ty t =
  let mty = S.get_type t and alpha_l = S.get_alpha_l t in
  StrSet.diff (fv_mty mty) (StrSet.of_list alpha_l)

let fv_ty_l ty_l = List.fold_left (fun out ty -> StrSet.union (fv_ty ty) out) StrSet.empty ty_l

let fr_r r out=
  match r with
  | S.RRgn _ -> StrSet.empty
  | S.RAlpha rgn -> StrSet.singleton rgn

let fr_mty mty =
  let fr_r r out =
    match r with
    | S.RRgn _ -> out
    | S.RAlpha rgn -> StrSet.add rgn out
  in
  let rec loop mty out =
    match mty with
    | S.TAlpha _ | S.TInt | S.TBool | S.TUnit -> out
    | S.THnd r -> fr_r r out
    | S.TFun (mty_l, mty2, r) ->
      List.fold_left (fun out mty -> loop mty out) (loop mty2 (fr_r r out)) mty_l
    | S.TCouple (mty1, mty2, r) -> loop mty1 (loop mty2 (fr_r r out))
    | S.TList (_, mty1, r) | S.TTree (_, _, mty1, r) | S.TRef (_, mty1, r) -> loop mty1 (fr_r r out)
  in loop mty StrSet.empty

let fr_ty t =
  let mty = S.get_type t and rgn_l = S.get_rgn_l t in
  StrSet.diff (fr_mty mty) (StrSet.of_list rgn_l)

let fr_ty_l ty_l = List.fold_left (fun out ty -> StrSet.union (fr_ty ty) out) StrSet.empty ty_l

let apply_r sr r =
  match r with
  | S.RRgn _ -> r
  | S.RAlpha rgn -> (try StrMap.find rgn sr with Not_found -> r)

let rec apply_m s mty =
  let st, sr = s in
  match mty with
  | S.TAlpha a -> (try StrMap.find a st with Not_found -> S.TAlpha a)
  | S.TInt | S.TBool | S.TUnit -> mty
  | S.THnd r -> S.THnd (apply_r sr r)
  | S.TFun(mty_l, mty2, r) ->
    S.TFun (List.map (fun mty -> apply_m s mty) mty_l, apply_m s mty2, apply_r sr r)
  | S.TCouple (mty1, mty2, r) -> S.TCouple (apply_m s mty1, apply_m s mty2, apply_r sr r)
  | S.TList (ls, mty1, r) -> S.TList (ls, apply_m s mty1, apply_r sr r)
  | S.TTree (lsn, lsd, mty1, r) -> S.TTree (lsn, lsd, apply_m s mty1, apply_r sr r)
  | S.TRef (id, mty1, r) -> S.TRef (id, apply_m s mty1, apply_r sr r)

let remove_subs alpha_l rgn_l s =
  let st, sr = s in
  List.fold_left (fun out a -> StrMap.remove a out) st alpha_l,
  List.fold_left (fun out r -> StrMap.remove r out) sr rgn_l

let apply s t =
  let te = S.get_term t and mty = S.get_type t and alpha_l = S.get_alpha_l t and rgn_l = S.get_rgn_l t in
  S.mk_term te (apply_m (remove_subs alpha_l [] s) mty) alpha_l rgn_l

let subs_empty = StrMap.empty, StrMap.empty

let subs_of_rsubs sr = StrMap.empty, sr

let remove_env env var = StrMap.remove var env

let fv_env env = fv_ty_l (List.rev_map snd (StrMap.bindings env))

let fr_env env = fr_ty_l (List.rev_map snd (StrMap.bindings env))

let apply_env s env = StrMap.map (apply s) env

let generalize env te mty =
  S.mk_term
    te
    mty
    (StrSet.elements (StrSet.diff (fv_mty mty) (fv_env env)))
    (StrSet.elements (StrSet.diff (fr_mty mty) (fr_env env)))

let instanciate t =
  let te = S.get_term t and mty = S.get_type t and alpha_l = S.get_alpha_l t and rgn_l = S.get_rgn_l t in
  let alpha_l_ty = List.map (fun _ -> S.TAlpha(mk_var ())) alpha_l in
  let rgn_l_r = List.map (fun _ -> S.RAlpha(mk_rgn ())) rgn_l in
  let st =
    List.fold_left2
      (fun out alpha ty_alpha -> StrMap.add alpha ty_alpha out)
      StrMap.empty alpha_l alpha_l_ty
  in
  let sr =
    List.fold_left2
      (fun out rgn r_rgn -> StrMap.add rgn r_rgn out)
      StrMap.empty rgn_l rgn_l_r
  in
  let s = st, sr in
  S.mk_term te (apply_m s mty) [] []

let varbind alpha mty =
  match mty with
  | S.TAlpha(alpha') when alpha = alpha' -> subs_empty
  | _ ->
    if StrSet.mem alpha (fv_mty mty) then
      raise (S.Type_Error(Printf.sprintf "Varbind : %s occurs in %s      %s"
                                    alpha
                                    (S.show_rcaml_type mty)
                                    (strset_str (fv_mty mty))))
    else
      StrMap.singleton alpha mty, StrMap.empty

let rgnbind r1 r2 =
  match r1, r2 with
  | S.RRgn(rgn1), S.RRgn(rgn2) ->
    if rgn1 = rgn2 then
      subs_empty
    else
      raise (S.Type_Error "rgnbind")
  | S.RAlpha(rgn1), S.RRgn(rgn2) -> StrMap.empty, StrMap.singleton rgn1 r2
  | S.RRgn(rgn1), S.RAlpha(rgn2) -> StrMap.empty, StrMap.singleton rgn2 r1
  | S.RAlpha(rgn1), S.RAlpha(rgn2) ->
    if rgn1 = rgn2 then
      subs_empty
    else
      StrMap.empty, StrMap.singleton rgn1 r2

let rec mgu mty1 mty2 =
  match mty1, mty2 with
  | S.TInt, S.TInt | S.TBool, S.TBool | S.TUnit, S.TUnit -> subs_empty
  | S.THnd(r1), S.THnd(r2) -> rgnbind r1 r2
  | S.TAlpha(a1), _ -> varbind a1 mty2
  | _, S.TAlpha(a2) -> varbind a2 mty1
  | S.TFun(arg_l1, dst1, r1), S.TFun(arg_l2, dst2, r2) -> begin
    try
      let s1 =
        List.fold_left2
          (fun s_out arg1 arg2 -> compose_subs (mgu arg1 arg2) s_out)
          subs_empty arg_l1 arg_l2
      in
      let s2 = mgu (apply_m s1 dst1) (apply_m s1 dst2) in
      let s3 = rgnbind r1 r2 in
      compose_subs s3 (compose_subs s1 s2)
    with Invalid_argument(str) ->
      raise (S.Type_Error ("Unification of Functions, different number of arguments : " ^ str))
  end
  | S.TCouple(mty1, mty2, r), S.TCouple(mty1', mty2', r') ->
    let s1 = mgu mty1 mty1' in
    let s2 = mgu (apply_m s1 mty2) (apply_m s1 mty2') in
    let s3 = rgnbind r r' in
    compose_subs s3 (compose_subs s1 s2)
  | S.TList(_, mty1, r), S.TList(_, mty1', r')
  | S.TTree(_, _, mty1, r), S.TTree(_, _, mty1', r')
  | S.TRef(_, mty1, r), S.TRef(_, mty1', r') ->
    let s1 = mgu mty1 mty1' in
    let s2 = rgnbind r r' in
    compose_subs s1 s2
  | _ -> raise (S.Type_Error(Printf.sprintf "Mgu %s %s" (S.show_rcaml_type mty1) (S.show_rcaml_type mty2)))

and compose_subs s1 s2 =
  if s1 = subs_empty then s2
  else if s2 = subs_empty then s1
  else (
  (* Printf.printf "\nCALL compose_subs : %s\n%s\n\n" (str_of_subs s2) (str_of_subs s1); *)
  let st1, sr1 = s1 in
  let st2, sr2 = s2 in
  let acc_s = ref subs_empty in
  (* Printf.printf "\nSTEP compose_subs : %s\n%s\n\n" (str_of_subs ((StrMap.map (apply_m s1) st2), sr2)) (str_of_subs s1); *)
  let st = StrMap.union
    (fun k mty1 mty2 ->
      (* Printf.printf "FLAG"; *)
      let s = mgu mty1 mty2 in
      acc_s := compose_subs s !acc_s;
      let out = apply_m s mty1 in
      (* Printf.printf "\n\ncompose subs %s : %s %s -> %s\n%s\n\n" k (S.show_rcaml_type mty1) (S.show_rcaml_type mty2) (S.show_rcaml_type out) (str_of_subs s); *)
      Some(out)) (StrMap.map (apply_m s1) st2) st1 in
  let sr = StrMap.union
    (fun r rgn1 rgn2 ->
      let s = mgu (S.THnd(rgn1)) (S.THnd(rgn2)) in
      let st, sr = s in
      acc_s := compose_subs s !acc_s;
      let out = apply_r sr rgn1 in
      (* Printf.printf "\n\ncompose subs %s : %s %s -> %s\n%s\n\n" r (S.show_regions rgn1) (S.show_regions rgn2) (S.show_regions out) (str_of_subs s); *)
      Some(rgn1))
    (StrMap.map (apply_r sr1) sr2) sr1 in
  compose_subs !acc_s (st, sr)
)

let remove_env env var = StrMap.remove var env

let get_rgn mty =
  match mty with
  |S.THnd(r) -> r
  |_ -> S.RRgn(mk_rgn ())

(***********)

let rec type_infer env t =
  let te = S.get_term t in
(*   Printf.printf "--------- TYPING PROCCES ------------\n%s\n\n" (S.show_term t); *)
  match te with
  | S.Var var -> begin
    try
(*Printf.printf "@@@@@@@@@@ VAR %s ENV\n%s\n\n" var (strmap_str env S.show_rcaml_type_poly);*)
      let t' = instanciate (StrMap.find var env) in
      subs_empty, generalize env (S.get_term t') (S.get_type t')
      (* S.mk_term (S.Var(var)) (generalize env (instanciate (StrMap.find var env))) *)
    with Not_found -> raise (S.Type_Error "Type_infer")
  end
  | S.Unit -> subs_empty, generalize env te S.TUnit
  | S.Bool b -> subs_empty, generalize env te S.TBool
  | S.Int i -> subs_empty, generalize env te S.TInt
  | S.Binop (op, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer (apply_env s1 env) t2 in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let s3 = mgu (apply_m s1 mty1) S.TInt in
    let s4 = mgu (apply_m s2 mty2) S.TInt in
    let s = compose_subs s4 (compose_subs s3 (compose_subs s2 s1)) in
    s, generalize env (S.Binop (op, t1', t2')) S.TInt
  | S.Not t1 ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let s2 = mgu (apply_m s1 mty1) S.TBool in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Not t1') S.TBool
  | S.Neg t1 ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let s2 = mgu (apply_m s1 mty1) S.TInt in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Neg t1') S.TInt
  | S.Comp (c, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer (apply_env s1 env) t2 in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let s = compose_subs s2 s1 in
    let s =
      match c with
      | S.Ceq | S.Cneq ->
        let s3 = mgu (apply_m s mty1) (apply_m s mty2) in
        compose_subs s3 s
      | _ ->
        let s3 = mgu (apply_m s1 mty1) S.TInt in
        let s4 = mgu (apply_m s2 mty2) S.TInt in
        compose_subs s4 (compose_subs s3 s)
    in
    s, generalize env (S.Comp (c, t1', t2')) S.TBool
  | S.Fun (f, x_l, t1, t2, pot) ->
    let a_l = List.rev_map (fun _ -> S.TAlpha(mk_var ())) x_l in
    let env' =
      List.fold_left2
        (fun env x mty -> StrMap.add x (S.mk_term (S.Var x) mty [] []) env)
        env x_l a_l
    in
    let s1, t1' = type_infer env' t1 in
    let s2, t2' = type_infer (apply_env s1 env') t2 in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let r = S.RAlpha(mk_rgn ()) in
    let s3 = mgu (apply_m s2 mty2) (S.THnd(r)) in
    let s = compose_subs s3 (compose_subs s2 s1) in
    s, generalize env
         (S.Fun (f, x_l, t1', t2', pot))
         (S.TFun (List.map (fun mty -> apply_m s mty) a_l, apply_m s mty1, apply_r (snd s) r))
  | S.App (t1, t2_l) ->
    let mty = S.TAlpha(mk_var ()) in
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let s2, t2_l' =
      List.fold_left
        (fun (s, t_l) t ->
          let tmp_s, tmp_t = type_infer (apply_env s env) t in
          compose_subs tmp_s s, tmp_t::t_l)
        (subs_empty, [])
        t2_l
    in
    let t2_l' = List.rev t2_l' in
    let ty_t2_l = List.map S.get_type t2_l' in
    let s3 = mgu (apply_m s2 mty1) (S.TFun(ty_t2_l, mty, S.RAlpha(mk_rgn ()))) in
    let s = compose_subs s3 (compose_subs s2 s1) in
    s, generalize env (S.App (t1', t2_l')) (apply_m s mty)
  | S.If (t1, t2, t3) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let s1' = mgu (apply_m s1 mty1) S.TBool in
    let env = apply_env s1' env in
    let s2, t2' = type_infer env t2 in
    let mty2 = S.get_type t2' in
    let env = apply_env s2 env in
    let s3, t3' = type_infer env t3 in
    let mty3 = S.get_type t3' in
    (* Printf.printf "((((((((((((((((((( IF TYPAGE DES BRANCHES TERMINE !!!!\n\n"; *)
    let s4 = mgu (apply_m s2 mty2) (apply_m s3 mty3) in
    let s = compose_subs s4 (compose_subs s3 (compose_subs s2 (compose_subs s1' s1))) in
    s, generalize env (S.If (t1', t2', t3')) (apply_m s mty2)
  | S.MatchList (t_match, t_nil, x, xs, t_cons) ->
    let s1, t_match' = type_infer env t_match in
    let mty_match = S.get_type t_match' in
    let a1 = S.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty_match) (S.TList(None, a1, S.RAlpha(mk_rgn ()))) in
    let s = compose_subs s1 s2 in
    let env = apply_env s env in
    let s3, t_nil' = type_infer env t_nil in
    let env = apply_env s3 env in
    let env' =
      StrMap.add
        x (S.mk_term (S.Var x) (apply_m s a1) [] [])
        (StrMap.add xs (S.mk_term (S.Var xs) (S.TList(None, apply_m s a1, S.RAlpha(mk_rgn ()))) [] []) env)
    in
    let s4, t_cons' = type_infer env' t_cons in
    let mty_nil = S.get_type t_nil' in
    let mty_cons = S.get_type t_cons' in
    let s = compose_subs s4 (compose_subs s3 s) in
    let s5 = mgu (apply_m s mty_nil) (apply_m s mty_cons) in
    let s = compose_subs s5 s in
    s, generalize env (S.MatchList (t_match', t_nil', x, xs, t_cons')) (apply_m s mty_cons)
  | S.MatchTree (t_match, t_leaf, x, tl, tr, t_node) ->
    let s1, t_match' = type_infer env t_match in
    let mty_match = S.get_type t_match' in
    let a1 = S.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty_match) (S.TTree(None, None, a1, S.RAlpha(mk_rgn ()))) in
    let s = compose_subs s1 s2 in
    let env = apply_env s env in
    let s3, t_leaf' = type_infer env t_leaf in
    let env = apply_env s3 env in
    let env' =
      StrMap.add
        x (S.mk_term (S.Var x) (apply_m s a1) [] [])
        (StrMap.add
          tl (S.mk_term (S.Var tl) (S.TTree(None, None, apply_m s a1, S.RAlpha(mk_rgn ()))) [] [])
          (StrMap.add tr (S.mk_term (S.Var tr) (S.TTree(None, None, apply_m s a1, S.RAlpha(mk_rgn ()))) [] []) env))
    in
    let s4, t_node' = type_infer env' t_node in
    let mty_leaf = S.get_type t_leaf' in
    let mty_node = S.get_type t_node' in
    let s = compose_subs s4 (compose_subs s3 s) in
    let s5 = mgu (apply_m s mty_leaf) (apply_m s mty_node) in
    let s = compose_subs s5 s in
    s, generalize env (S.MatchTree (t_match', t_leaf', x, tl, tr, t_node')) (apply_m s mty_node)
  | S.Let (x, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let env' = StrMap.add x (generalize (apply_env s1 env) (S.Var x) mty1) env in
    let s2, t2' = type_infer (apply_env s1 env') t2 in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Let (x, t1', t2')) (S.get_type t2')
  | S.Letrec (f, t1, t2) ->
    let a = S.TAlpha(mk_var ()) in
    let env' = StrMap.add f (S.mk_term (S.Var f) a [] []) env in
    let s1, t1' = type_infer env' t1 in
    let mty1 = S.get_type t1' in
    let s1' = mgu (apply_m s1 a) (apply_m s1 mty1) in
    let s = compose_subs s1' s1 in
    let env'' = StrMap.add f (generalize (apply_env s env) (S.Var f) (apply_m s mty1)) env' in
    let s2, t2' = type_infer (apply_env s env'') t2 in
    let s = compose_subs s2 s in
    s, generalize env (S.Letrec (f, t1', t2')) (S.get_type t2')
  | S.Pair (t1, t2, t3) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env = apply_env s2 env in
    let s3, t3' = type_infer env t3 in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let mty3 = S.get_type t3' in
    let r = S.RAlpha(mk_rgn ()) in
    let s = compose_subs s3 (compose_subs s2 s1) in
    let s4 = mgu (apply_m s mty3) (S.THnd(r)) in
    let s = compose_subs s4 s in
    s, generalize env (S.Pair (t1', t2', t3')) (S.TCouple(mty1, mty2, r))
  | S.Fst t1 ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let a1 = S.TAlpha(mk_var ()) in
    let a2 = S.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (S.TCouple(a1, a2, S.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Fst t1') (apply_m s a1)
  |S.Snd t1 ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let a1 = S.TAlpha(mk_var ()) in
    let a2 = S.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (S.TCouple(a1, a2, S.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Snd t1') (apply_m s a2)
  |S.Hd t1 ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let tmp = mk_var () in
    let a1 = S.TAlpha(tmp) in
    let s2 = mgu (apply_m s1 mty1) (S.TList(None, a1, S.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
  let st, sr = s in
  (* Printf.printf "\n\n\n&&&&&&&&&&&&& HD SUB (%s) :\n%s\n\nSUBSTITUTION RGN :\n%s\n\n" tmp (strmap_str st S.show_rcaml_type) (strmap_str sr S.show_regions); *)
    s, generalize env (S.Hd t1') a1
  | S.Tl t1 ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let a1 = S.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (S.TList(None, a1, S.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Tl t1') (apply_m s mty1)
  | S.Nil -> subs_empty, generalize env te (S.TList(None, S.TAlpha(mk_var ()), S.RAlpha(mk_rgn ())))
  | S.Leaf -> subs_empty, generalize env te (S.TTree(None, None, S.TAlpha(mk_var ()), S.RAlpha(mk_rgn ())))
  | S.Cons (t1, t2, t3) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env  = apply_env s2 env in
    let s3, t3' = type_infer env t3 in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let mty3 = S.get_type t3' in
    let r = S.RAlpha(mk_rgn ()) in
    let s = compose_subs s3 (compose_subs s2 s1) in
    let s4 = mgu (apply_m s mty2) (S.TList(None, apply_m s mty1, S.RAlpha(mk_rgn ()))) in
    let s5 = mgu (apply_m s mty3) (S.THnd r) in
    let s = compose_subs s5 (compose_subs s4 s) in
    s, generalize env (S.Cons (t1', t2', t3')) (apply_m s (S.TList (None, apply_m s mty1, r)))
  | S.Node (t1, t2, t3, t4) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env  = apply_env s2 env in
    let s3, t3' = type_infer env t3 in
    let env  = apply_env s3 env in
    let s4, t4' = type_infer env t4 in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let mty3 = S.get_type t3' in
    let mty4 = S.get_type t4' in
    let r = S.RAlpha(mk_rgn ()) in
    let s = compose_subs s4 (compose_subs s3 (compose_subs s2 s1)) in
    let s5 = mgu (apply_m s mty2) (S.TTree(None, None, apply_m s mty1, S.RAlpha(mk_rgn ()))) in
    let s6 = mgu (apply_m s mty3) (S.TTree(None, None, apply_m s mty1, S.RAlpha(mk_rgn ()))) in
    let s7 = mgu (apply_m s mty4) (S.THnd r) in
    let s = compose_subs s7 (compose_subs s6 (compose_subs s5 s)) in
    s, generalize env (S.Node (t1', t2', t3', t4')) (apply_m s (S.TTree (None, None, apply_m s mty1, r)))
  | S.Ref (t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env  = apply_env s2 env in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let r = S.RAlpha(mk_rgn ()) in
    let s = compose_subs s2 s1 in
    let s3 = mgu (apply_m s mty2) (S.THnd(r)) in
    let s = compose_subs s3 s in
    s, generalize env (S.Ref (t1', t2')) (apply_m s (S.TRef(0, apply_m s mty1, r)))
  | S.Assign (t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env  = apply_env s2 env in
    let s = compose_subs s2 s1 in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let r = S.RAlpha(mk_rgn ()) in
    Printf.printf "Assign : %s\n" (S.show_regions r);
    let s3 = mgu (S.TRef(0, apply_m s mty2, r)) (apply_m s mty1) in
    let s = compose_subs s3 s in
    s, generalize env (S.Assign (t1', t2')) S.TUnit
  | S.Deref t1 ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let tmp = mk_var () in
    let a1 = S.TAlpha(tmp) in
    let s2 = mgu (apply_m s1 mty1) (S.TRef(0, a1, S.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Deref t1') a1
  | S.Newrgn -> subs_empty, generalize env te (S.THnd (S.RRgn (mk_rgn ())))
  | S.Aliasrgn (t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer env t2 in
    let mty1 = S.get_type t1' in
    let mty2 = S.get_type t2' in
    let s = compose_subs s2 s1 in
    let s3 = mgu (apply_m s mty1) (S.THnd (S.RAlpha (mk_rgn ()))) in
    let s = compose_subs s3 s in
    s, generalize env (S.Aliasrgn (t1', t2')) (apply_m s mty2)
  | S.Freergn t1 ->
    let s1, t1' = type_infer env t1 in
    let mty1 = S.get_type t1' in
    let s2 = mgu (apply_m s1 mty1) (S.THnd (S.RAlpha (mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Freergn t1') S.TUnit
  | S.Sequence (t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer env t2 in
    let mty2 = S.get_type t2' in
    let s = compose_subs s2 s1 in
    s, generalize env (S.Sequence (t1', t2')) (apply_m s mty2)

let normalize_ty mty =
  mty, StrSet.elements (fv_mty mty), StrSet.elements (fr_mty mty)

let iter_fun f x =
  let rec loop x old = if x = old then x else loop (f x) x in
  loop (f x) x

let rec subs_term s t =
  let te = S.get_term t and mty = S.get_type t and alpha_l = S.get_alpha_l t and rgn_l = S.get_rgn_l t in
  let mty', alpha_l', rgn_l' = normalize_ty (iter_fun (apply_m s) mty) in
  S.mk_term
    (match te with
     | S.Unit | S.Bool _ | S.Int _ | S.Var _ | S.Newrgn -> te
     | S.Binop (op, t1, t2) -> S.Binop (op, subs_term s t1, subs_term s t2)
     | S.Not t1 -> S.Not (subs_term s t1)
     | S.Neg t1 -> S.Neg (subs_term s t1)
     | S.Comp (c, t1, t2) -> S.Comp (c, subs_term s t1, subs_term s t2)
     | S.Fun (f, arg_l, t1, t2, pot) -> S.Fun (f, arg_l, subs_term s t1, subs_term s t2, pot)
     | S.App (t1, t_l) -> S.App (subs_term s t1, List.map (subs_term s) t_l)
     | S.If (t1, t2, t3) -> S.If (subs_term s t1, subs_term s t2, subs_term s t3)
     | S.MatchList (t_match, t_nil, x, xs, t_cons) ->
       S.MatchList (subs_term s t_match, subs_term s t_nil, x, xs, subs_term s t_cons)
     | S.MatchTree (t_match, t_leaf, x, tl, ts, t_node) ->
       S.MatchTree (subs_term s t_match, subs_term s t_leaf, x, tl, ts, subs_term s t_node)
     | S.Let (x, t1, t2) -> S.Let (x, subs_term s t1, subs_term s t2)
     | S.Letrec (f, t1, t2) -> S.Letrec (f, subs_term s t1, subs_term s t2)
     | S.Pair (t1, t2, t3) -> S.Pair (subs_term s t1, subs_term s t2, subs_term s t3)
     | S.Fst t1 -> S.Fst (subs_term s t1)
     | S.Snd t1 -> S.Snd (subs_term s t1)
     | S.Hd t1 -> S.Hd (subs_term s t1)
     | S.Tl t1 -> S.Tl (subs_term s t1)
     | S.Nil -> S.Nil
     | S.Leaf -> S.Leaf
     | S.Cons (t1, t2, t3) -> S.Cons (subs_term s t1, subs_term s t2, subs_term s t3)
     | S.Node (t1, t2, t3, t4) -> S.Node (subs_term s t1, subs_term s t2, subs_term s t3, subs_term s t4)
     | S.Ref (t1, t2) -> S.Ref (subs_term s t1, subs_term s t2)
     | S.Assign (t1, t2) -> S.Assign (subs_term s t1, subs_term s t2)
     | S.Deref t1 -> S.Deref (subs_term s t1)
     | S.Aliasrgn (t1, t2) -> S.Aliasrgn (subs_term s t1, subs_term s t2)
     | S.Freergn t1 -> S.Freergn (subs_term s t1)
     | S.Sequence (t1, t2) -> S.Sequence (subs_term s t1, subs_term s t2))
    mty' alpha_l' rgn_l'

let type_inference env t =
  let s, t = type_infer env t in
  let st, sr = s in
  Printf.printf "SUBSTITUTION TYPE :\n%s\n\nSUBSTITUTION RGN :\n%s\n\n" (strmap_str st S.show_rcaml_type) (strmap_str sr S.show_regions);
  subs_term s t

let process t = type_inference StrMap.empty t
