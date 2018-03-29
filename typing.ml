open Util

exception Mutual_Def

module S = Ast
module T = Type

(* ALGORITHM W *)

let fv_mty mty =
  let rec loop mty out =
    match mty with
    |T.TAlpha(a) -> StrSet.add a out
    |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> out
    |T.TFun(mty_l, mty2, _) -> List.fold_left (fun out mty -> loop mty out) (loop mty2 out) mty_l
    |T.TCouple(mty1, mty2, _) -> loop mty1 (loop mty2 out)
    |T.TList(mty1, _) -> loop mty1 out
    |T.TRef(mty1, _) -> loop mty1 out
  in loop mty StrSet.empty

let fv_ty (T.TPoly(alpha_l, mty)) = StrSet.diff (fv_mty mty) (StrSet.of_list alpha_l)

let fv_ty_l ty_l = List.fold_left (fun out ty -> StrSet.union (fv_ty ty) out) StrSet.empty ty_l

let rec apply_m s mty =
  match mty with
  |T.TAlpha(a) -> (try StrMap.find a s with Not_found -> T.TAlpha(a))
  |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> mty
  |T.TFun(mty_l, mty2, r) -> T.TFun(List.map (fun mty -> apply_m s mty) mty_l, apply_m s mty2, r)
  |T.TCouple(mty1, mty2, r) -> T.TCouple(apply_m s mty1, apply_m s mty2, r)
  |T.TList(mty1, r) -> T.TList(apply_m s mty1, r)
  |T.TRef(mty1, r) -> T.TRef(apply_m s mty1, r)

let apply s (T.TPoly(alpha_l, mty)) = T.TPoly(alpha_l, apply_m (List.fold_left (fun out a -> StrMap.remove a out) s alpha_l) mty)

let subs_empty = StrMap.empty

let compose_subs s1 s2 = StrMap.union (fun _ mty1 _ -> Some(mty1)) (StrMap.map (apply_m s1) s2) s1

let remove_env env var = StrMap.remove var env

let fv_env env = fv_ty_l (List.rev_map snd (StrMap.bindings env))

let apply_env s env = StrMap.map (apply s) env

let generalize env mty = T.TPoly(StrSet.elements (StrSet.diff (fv_mty mty) (fv_env env)), mty)

let instanciate (T.TPoly(alpha_l, mty)) =
  let alpha_l_ty = List.rev_map (fun _ -> T.TAlpha(mk_var ())) alpha_l in
  let s = List.fold_left2 (fun out alpha ty_alpha -> StrMap.add alpha ty_alpha out) StrMap.empty alpha_l alpha_l_ty in
  apply_m s mty

let varbind alpha mty =
  match mty with
  |T.TAlpha(alpha') when alpha = alpha' -> subs_empty
  |_ ->
    if StrSet.mem alpha (fv_mty mty) then
      raise (T.Type_Error(Printf.sprintf "Varbind : %s occurs in %s      %s" alpha (T.show_rcaml_type mty) (strset_str (fv_mty mty))))
    else
      StrMap.singleton alpha mty

let rec mgu mty1 mty2 =
  match mty1, mty2 with
  |T.TInt, T.TInt |T.TBool, T.TBool |T.TUnit, T.TUnit |T.THnd(_), T.THnd(_) -> subs_empty
  |T.TAlpha(a1), _ -> varbind a1 mty2
  |_, T.TAlpha(a2) -> varbind a2 mty1
  |T.TFun(arg_l1, dst1, _), T.TFun(arg_l2, dst2, _) -> begin
    try
      let s1 = List.fold_left2 (fun s_out arg1 arg2 -> compose_subs (mgu arg1 arg2) s_out) subs_empty arg_l1 arg_l2 in
      let s2 = mgu (apply_m s1 dst1) (apply_m s1 dst2) in
      compose_subs s1 s2
    with Invalid_argument(str) -> raise (T.Type_Error ("Unification of Functions, different number of arguments : " ^ str))
  end
  |T.TCouple(mty1, mty2, _), T.TCouple(mty1', mty2', _) ->
    let s1 = mgu mty1 mty1' in
    let s2 = mgu (apply_m s1 mty2) (apply_m s1 mty2') in
    compose_subs s1 s2
  |T.TList(mty1, _), T.TList(mty1', _) |T.TRef(mty1, _), T.TRef(mty1', _) -> mgu mty1 mty1'
  |_ -> raise (T.Type_Error("Mgu"))

let mty_of (T.TPoly(_, mty)) = mty

let to_poly mty = T.TPoly([], mty)

(***********)

let rec type_infer env t =
  match t with
  |S.Var(var) -> begin
    try
      subs_empty, T.mk_term (T.Var(var)) (generalize env (instanciate (StrMap.find var env)))
    with Not_found -> raise (T.Type_Error "Type_infer")
  end
  |S.Unit -> subs_empty, T.mk_term T.Unit (generalize env T.TUnit)
  |S.Bool(b) -> subs_empty, T.mk_term (T.Bool(b)) (generalize env T.TBool)
  |S.Int(i) -> subs_empty, T.mk_term (T.Int(i)) (generalize env T.TInt)
  |S.Binop(op, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer (apply_env s1 env) t2 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let s3 = mgu (apply_m s1 mty1) T.TInt in
    let s4 = mgu (apply_m s2 mty2) T.TInt in
    compose_subs s1 (compose_subs s2 (compose_subs s3 s4)), T.mk_term (T.Binop(op, t1', t2')) (generalize env T.TInt)
  |S.Not(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s2 = mgu (apply_m s1 mty1) T.TBool in
    compose_subs s1 s2, T.mk_term (T.Not(t1')) (generalize env T.TBool)
  |S.Neg(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s2 = mgu (apply_m s1 mty1) T.TInt in
    compose_subs s1 s2, T.mk_term (T.Neg(t1')) (generalize env T.TInt)
  |S.Comp(c, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer (apply_env s1 env) t2 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let s3 = mgu (apply_m s1 mty1) T.TBool in
    let s4 = mgu (apply_m s2 mty2) T.TBool in
    compose_subs s1 (compose_subs s2 (compose_subs s3 s4)), T.mk_term (T.Comp(c, t1', t2')) (generalize env T.TBool)
  |S.Fun(x_l, t1, t2) ->
    let a_l = List.rev_map (fun _ -> T.TAlpha(mk_var ())) x_l in
    let env' = List.fold_left2 (fun env x mty -> StrMap.add x (T.TPoly([], mty)) env) env x_l a_l in
    let s1, t1' = type_infer env' t1 in
    let s2, t2' = type_infer (apply_env s1 env') t2 in
    let mty1 = mty_of (T.get_type t1') in
    let s = compose_subs s1 s2 in
    s, T.mk_term (T.Fun(x_l, t1', t2')) (generalize env (T.TFun(List.map (fun mty -> apply_m s mty) a_l, mty1, "DUMB REGION")))
  |S.App(t1, t2_l) ->
    let mty = T.TAlpha(mk_var ()) in
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s2, t2_l' =
      List.fold_left
        (fun (s, t_l) t ->
          let tmp_s, tmp_t = type_infer (apply_env s env) t in
          compose_subs tmp_s s, tmp_t::t_l)
        (s1, [])
        t2_l
    in
    let t2_l' = List.rev t2_l' in
    let ty_t2_l = List.map (fun t -> mty_of (T.get_type t)) t2_l' in
    let s3 = mgu (apply_m s2 mty1) (T.TFun(ty_t2_l, mty, mk_var ())) in
    compose_subs s3 (compose_subs s2 s1), T.mk_term (T.App(t1', t2_l')) (generalize env (apply_m s3 mty))
  |S.If(t1, t2, t3) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s1' = mgu (apply_m s1 mty1) T.TBool in
    let env = apply_env s1' env in
    let s2, t2' = type_infer env t2 in
    let mty2 = mty_of (T.get_type t2') in
    let env = apply_env s2 env in
    let s3, t3' = type_infer env t3 in
    let mty3 = mty_of (T.get_type t3') in
    let s4 = mgu (apply_m s2 mty2) (apply_m s3 mty3) in
    compose_subs s1' (compose_subs s2 (compose_subs s3 s4)), T.mk_term (T.If(t1', t2', t3')) (generalize env (apply_m s4 mty2))
  |S.Let(x, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let env' = StrMap.add x (generalize (apply_env s1 env) mty1) env in
    let s2, t2' = type_infer (apply_env s1 env') t2 in
    compose_subs s1 s2, T.mk_term (T.Let(x, t1', t2')) (T.get_type t2')
  |S.Letrec(f, t1, t2) ->
    let a = mk_var () in
    let env' = StrMap.add f (T.TPoly([], T.TAlpha(a))) env in
    let s1, t1' = type_infer env' t1 in
    let mty1 = mty_of (T.get_type t1') in
    let env'' = StrMap.add f (generalize (apply_env s1 env') mty1) env' in
    let s2, t2' = type_infer (apply_env s1 env'') t2 in
    compose_subs s1 s2, T.mk_term (T.Letrec(f, t1', t2')) (T.get_type t2')
  |S.Pair(t1, t2, t3) -> assert false
  |S.Fst(t1) -> assert false
  |S.Snd(t1) -> assert false
  |S.Hd(t1) -> assert false
  |S.Tl(t1) -> assert false
  |S.Nil(t1) -> assert false
  |S.Cons(t1, t2, t3) -> assert false
  |S.Ref(t1, t2) -> assert false
  |S.Assign(t1, t2) -> assert false
  |S.Deref(t1) -> assert false
  |S.Newrgn -> subs_empty, T.mk_term T.Newrgn (generalize env (T.THnd(mk_rgn ())))
  |S.Aliasrgn(t1, t2) -> assert false
  |S.Freergn(t1) -> assert false

let subs s (T.TPoly(alpha_l, mty)) =
  let rec iter mty old_mty =
    Printf.printf "subs %s\n" (T.show_rcaml_type mty);
    if mty = old_mty then
      T.TPoly(StrSet.elements (fv_mty mty), mty)
    else
      iter (apply_m s mty) mty
  in
  Printf.printf "subs %s\n" (T.show_rcaml_type mty);
  iter (apply_m s mty) mty

let rec subs_term s t =
  T.mk_term
    (
      match T.get_term t with
      |T.Unit |T.Bool(_) |T.Int(_) |T.Var(_) |T.Newrgn -> T.get_term t
      |T.Binop(op, t1, t2) -> T.Binop(op, subs_term s t1, subs_term s t2)
      |T.Not(t1) -> T.Not(subs_term s t1)
      |T.Neg(t1) -> T.Neg(subs_term s t1)
      |T.Comp(c, t1, t2) -> T.Comp(c, subs_term s t1, subs_term s t2)
      |T.Fun(arg_l, t1, t2) -> T.Fun(arg_l, subs_term s t1, subs_term s t2)
      |T.App(t1, t_l) -> T.App(subs_term s t1, List.map (subs_term s) t_l)
      |T.If(t1, t2, t3) -> T.If(subs_term s t1, subs_term s t2, subs_term s t3)
      |T.Let(x, t1, t2) -> T.Let(x, subs_term s t1, subs_term s t2)
      |T.Letrec(f, t1, t2) -> T.Letrec(f, subs_term s t1, subs_term s t2)
      |T.Pair(t1, t2, t3) -> T.Pair(subs_term s t1, subs_term s t2, subs_term s t3)
      |T.Fst(t1) -> T.Fst(subs_term s t1)
      |T.Snd(t1) -> T.Snd(subs_term s t1)
      |T.Hd(t1) -> T.Hd(subs_term s t1)
      |T.Tl(t1) -> T.Tl(subs_term s t1)
      |T.Nil(t1) -> T.Nil(subs_term s t1)
      |T.Cons(t1, t2, t3) -> T.Cons(subs_term s t1, subs_term s t2, subs_term s t3)
      |T.Ref(t1, t2) -> T.Ref(subs_term s t1, subs_term s t2)
      |T.Assign(t1, t2) -> T.Assign(subs_term s t1, subs_term s t2)
      |T.Deref(t1) -> T.Deref(subs_term s t1)
      |T.Aliasrgn(t1, t2) -> T.Aliasrgn(subs_term s t1, subs_term s t2)
      |T.Freergn(t1) -> T.Freergn(subs_term s t1)
    )
    (subs s (T.get_type t))

let type_inference env t =
  let s, t = type_infer env t in
  subs_term s t

let type_term t = type_inference StrMap.empty t
