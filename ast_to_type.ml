open Util

module S = Ast
module T = Type

(* ALGORITHM W *)

let fv_mty mty =
  let rec loop mty out =
    match mty with
    |T.TAlpha(a) -> StrSet.add a out
    |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> out
    |T.TFun(mty_l, mty2, mty3) -> List.fold_left (fun out mty -> loop mty out) (loop mty2 out) mty_l
    |T.TCouple(mty1, mty2, mty3) -> loop mty1 (loop mty2 out)
    |T.TList(mty1, mty2) -> loop mty1 out
    |T.TRef(mty1, mty2) -> loop mty1 out
  in loop mty StrSet.empty

let fv_ty (T.TPoly(alpha_l, _, mty)) = StrSet.diff (fv_mty mty) (StrSet.of_list alpha_l)

let fv_ty_l ty_l = List.fold_left (fun out ty -> StrSet.union (fv_ty ty) out) StrSet.empty ty_l

let fr_mty mty =
  let rec loop mty out =
    match mty with
    |T.TInt |T.TBool |T.TUnit |T.TAlpha(_) -> out
    |T.THnd(r) -> StrSet.add r out
    |T.TFun(mty_l, mty2, mty3) -> List.fold_left (fun out mty -> loop mty out) (loop mty2 (loop mty3 out)) mty_l
    |T.TCouple(mty1, mty2, mty3) -> loop mty1 (loop mty2 (loop mty3 out))
    |T.TList(mty1, mty2) -> loop mty1 (loop mty2 out)
    |T.TRef(mty1, mty2) -> loop mty1 (loop mty2 out)
  in loop mty StrSet.empty

let fr_ty (T.TPoly(_, rgn_l, mty)) = StrSet.diff (fr_mty mty) (StrSet.of_list rgn_l)

let fr_ty_l ty_l = List.fold_left (fun out ty -> StrSet.union (fr_ty ty) out) StrSet.empty ty_l

let rgn_of_env env =
  StrSet.of_list
    (List.rev_map
      (fun (_, T.TPoly(_, _,T.THnd(r))) -> r)
      (StrMap.bindings (StrMap.filter (fun x (T.TPoly(_, _, mty)) -> match mty with |T.THnd(_) -> true |_ -> false) env)))

let rec apply_mty s mty =
  match mty with
  |T.TAlpha(a) -> (try StrMap.find a s with Not_found -> T.TAlpha(a))
  |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> mty
  |T.TFun(mty_l, mty2, mty3) -> T.TFun(List.map (fun mty -> apply_mty s mty) mty_l, apply_mty s mty2, apply_mty s mty3)
  |T.TCouple(mty1, mty2, mty3) -> T.TCouple(apply_mty s mty1, apply_mty s mty2, apply_mty s mty3)
  |T.TList(mty1, mty2) -> T.TList(apply_mty s mty1, apply_mty s mty2)
  |T.TRef(mty1, mty2) -> T.TRef(apply_mty s mty1, apply_mty s mty2)

let apply_m s mty =
  let rec loop mty old =
    if mty = old then
      mty
    else
      loop (apply_mty s mty) mty
  in loop (apply_mty s mty) mty

let apply s (T.TPoly(alpha_l, rgn_l, mty)) =
  T.TPoly(alpha_l, rgn_l, apply_m (List.fold_left (fun out a -> StrMap.remove a out) s alpha_l) mty)

let subs_empty = StrMap.empty

let compose_subs s1 s2 = StrMap.union (fun _ mty1 _ -> Some(mty1)) (StrMap.map (apply_m s1) s2) s1

let remove_env env var = StrMap.remove var env

let fv_env env = fv_ty_l (List.rev_map snd (StrMap.bindings env))

let apply_env s env = StrMap.map (apply s) env

let generalize env mty =
  let s = StrSet.diff (fv_mty mty) (fv_env env) in
  let rgn_l = StrSet.elements (StrSet.diff (fr_mty mty) (rgn_of_env env)) in
  Printf.printf "|||||||||||||||||||||||||||\n GEN FV_MTY :\n%s\n|||||||||||||||||||||\n\n" (strset_str (fv_mty mty));
  Printf.printf "|||||||||||||||||||||||||||\n GEN FV_ENV :\n%s\n|||||||||||||||||||||\n\n" (strset_str (fv_env env));
  Printf.printf "|||||||||||||||||||||||||||\n GEN ENV :\n%s\n|||||||||||||||||||||\n\n" (strset_str s);
  T.TPoly(StrSet.elements (StrSet.diff (fv_mty mty) (fv_env env)), rgn_l, mty)

let instanciate (T.TPoly(alpha_l, rgn_l, mty)) =
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
  |_ -> raise (T.Type_Error(Printf.sprintf "Mgu %s %s" (T.show_rcaml_type mty1) (T.show_rcaml_type mty2)))

let mty_of (T.TPoly(_, _, mty)) = mty

let to_poly mty = T.TPoly([], [], mty)

let get_rgn mty =
  match mty with
  |T.THnd(r) -> r
  |_ -> mk_rgn ()

(***********)

let rec type_infer env t =
  Printf.printf "--------- TYPING PROCCES ------------\n%s\n\n" (S.show_term t);
  match t with
  |S.Var(var) -> begin
    try
Printf.printf "---------- VAR NAME %s\n\n\n" var;
      let mty = StrMap.find var env in
Printf.printf "---------- VAR MTY %s\n\n\n" (T.show_rcaml_type_poly mty);
      let mty_ins = instanciate mty in
Printf.printf "---------- VAR MTY_INS %s\n\n\n" (T.show_rcaml_type mty_ins);
      let mty_gen = generalize env mty_ins in
Printf.printf "---------- VAR GEN %s\n\n\n" (T.show_rcaml_type_poly mty_gen);
      subs_empty, T.mk_term (T.Var(var)) mty_gen
      (*subs_empty, T.mk_term (T.Var(var)) (generalize env (instanciate (StrMap.find var env)))*)
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
    let s = compose_subs s1 s2 in
    let s =
      match c with
      |T.Ceq |T.Cneq ->
        let s3 = mgu (apply_m s mty1) (apply_m s mty2) in
        compose_subs s3 s
      |_ ->
        let s3 = mgu (apply_m s1 mty1) T.TBool in
        let s4 = mgu (apply_m s2 mty2) T.TBool in
        compose_subs s4 (compose_subs s3 s)
    in
Printf.printf "|||||||||||||||||||||||||||\n DEBUG :\n%s\n|||||||||||||||||||||\n\n" (strmap_str s (T.show_rcaml_type));
    s, T.mk_term (T.Comp(c, t1', t2')) (generalize env T.TBool)
  |S.Fun(x_l, t1, t2) ->
    let a_l = List.rev_map (fun _ -> T.TAlpha(mk_var ())) x_l in
    let env' = List.fold_left2 (fun env x mty -> StrMap.add x (T.TPoly([], [], mty)) env) env x_l a_l in
    let s1, t1' = type_infer env' t1 in
    let s2, t2' = type_infer (apply_env s1 env') t2 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let r = get_rgn mty2 in
    let s3 = mgu (apply_m s2 mty2) (T.THnd(r)) in
    let s = compose_subs s3 (compose_subs s1 s2) in
    s, T.mk_term (T.Fun(x_l, t1', t2')) (generalize env (T.TFun(List.map (fun mty -> apply_m s mty) a_l, mty1, T.THnd(r))))
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
    let s3 = mgu (apply_m s2 mty1) (T.TFun(ty_t2_l, mty, T.THnd(mk_rgn ()))) in
    let s = compose_subs s3 (compose_subs s2 s1) in
Printf.printf "ESTOYYYYYYYYYYYYYYYYY subs: %s\nty_t1': %s\n\n\n\n\n\n" (strmap_str s T.show_rcaml_type) (T.show_rcaml_type_poly (T.get_type t1'));
    compose_subs s3 (compose_subs s2 s1), T.mk_term (T.App(t1', t2_l')) (generalize env (apply_m s mty))
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
    let s = compose_subs s1 (compose_subs s1' (compose_subs s2 (compose_subs s3 s4))) in
Printf.printf "|||||||||||||||||||||||||||\n DEBUG :\n%s\n|||||||||||||||||||||\n\n" (strmap_str s (T.show_rcaml_type));
    s, T.mk_term (T.If(t1', t2', t3')) (generalize env (apply_m s4 mty2))
  |S.Let(x, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let env' = StrMap.add x (generalize (apply_env s1 env) mty1) env in
    let s2, t2' = type_infer (apply_env s1 env') t2 in
    compose_subs s1 s2, T.mk_term (T.Let(x, t1', t2')) (T.get_type t2')
  |S.Letrec(f, t1, t2) ->
    let a = mk_var () in
    let env' = StrMap.add f (T.TPoly([], [], T.TAlpha(a))) env in
    let s1, t1' = type_infer env' t1 in
    let mty1 = mty_of (T.get_type t1') in
    let infered_mty1 = apply_m s1 (T.TAlpha(a)) in
    Printf.printf "AQUIIIIIIIIIIIIIIIIIII %s ?= %s\n\n\n\n\n\n" (T.show_rcaml_type mty1) (T.show_rcaml_type infered_mty1);
    let s1' = mgu (apply_m s1 mty1) infered_mty1 in
    Printf.printf "BEFORE EVALUATION %s\n\n" (T.show_rcaml_type_poly (T.get_type t1'));
Printf.printf "|||||||||||||||||||||||||||\n BEFORE GEN :\n%s\n|||||||||||||||||||||\n\n" (strmap_str s1 (T.show_rcaml_type));
Printf.printf "|||||||||||||||||||||||||||\n ENV :\n%s\n|||||||||||||||||||||\n\n" (strmap_str env (T.show_rcaml_type_poly));
Printf.printf "|||||||||||||||||||||||||||\n ENV' :\n%s\n|||||||||||||||||||||\n\n" (strmap_str env' (T.show_rcaml_type_poly));
Printf.printf "|||||||||||||||||||||||||||\n APPLIED ENV :\n%s\n|||||||||||||||||||||\n\n" (strmap_str (apply_env s1 env) (T.show_rcaml_type_poly));
Printf.printf "|||||||||||||||||||||||||||\n APPLIED ENV' :\n%s\n|||||||||||||||||||||\n\n" (strmap_str (apply_env s1 env') (T.show_rcaml_type_poly));
    Printf.printf "EVALUATION ENV %s\n\n\n\n\n\n" (T.show_rcaml_type_poly (generalize (apply_env s1 env) mty1));
    Printf.printf "EVALUATION ENV' %s\n\n\n\n\n\n" (T.show_rcaml_type_poly (generalize (apply_env s1 env') mty1));
    let env'' = StrMap.add f (generalize (apply_env s1 env) mty1) env' in
    let s2, t2' = type_infer (apply_env s1 env'') t2 in
    let s = compose_subs s1' (compose_subs s1 s2) in
Printf.printf "|||||||||||||||||||||||||||\n DEBUG :\n%s\n|||||||||||||||||||||\n\n" (strmap_str s (T.show_rcaml_type));
    s, T.mk_term (T.Letrec(f, t1', t2')) (T.get_type t2')
  |S.Pair(t1, t2, t3) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env = apply_env s2 env in
    let s3, t3' = type_infer env t3 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let mty3 = mty_of (T.get_type t3') in
    let r = get_rgn mty3 in
    let s = compose_subs s3 (compose_subs s2 s1) in
    let s4 = mgu (apply_m s mty3) (T.THnd(r)) in
    let s = compose_subs s4 s in
    s, T.mk_term (T.Pair(t1', t2', t3')) (generalize env (T.TCouple(mty1, mty2, T.THnd(r))))
  |S.Fst(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let a1 = T.TAlpha(mk_var ()) in
    let a2 = T.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (T.TCouple(a1, a2, T.THnd(mk_rgn ()))) in
    let s = compose_subs s1 s2 in
    s, T.mk_term (T.Fst(t1')) (generalize env (apply_m s a1))
  |S.Snd(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let a1 = T.TAlpha(mk_var ()) in
    let a2 = T.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (T.TCouple(a1, a2, T.THnd(mk_rgn ()))) in
    let s = compose_subs s1 s2 in
    s, T.mk_term (T.Snd(t1')) (generalize env (apply_m s a2))
  |S.Hd(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let a1 = T.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (T.TList(a1, T.THnd(mk_rgn ()))) in
    let s = compose_subs s1 s2 in
    s, T.mk_term (T.Hd(t1')) (generalize env (apply_m s a1))
  |S.Tl(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let a1 = T.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (T.TList(a1, T.THnd(mk_rgn ()))) in
    let s = compose_subs s1 s2 in
    s, T.mk_term (T.Tl(t1')) (generalize env (apply_m s mty1))
  |S.Nil(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let tmp_a = mk_var () in
    let a1 = T.TAlpha(tmp_a) in
    Printf.printf "DEBUG !!!!!!!!!!!!!! %s \n\n" tmp_a;
    let r = get_rgn mty1 in
    let s2 = mgu a1 (apply_m s1 mty1) in
    let s = compose_subs s1 s2 in
Printf.printf "|||||||||||||||||||||||||||\n DEBUG :\n%s\n|||||||||||||||||||||\n\n" (strmap_str s (T.show_rcaml_type));
    s, T.mk_term (T.Nil(t1')) (generalize env (T.TList(T.TAlpha(mk_var ()), a1)))
  |S.Cons(t1, t2, t3) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env  = apply_env s2 env in
    let s3, t3' = type_infer env t3 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let mty3 = mty_of (T.get_type t3') in
    let r = get_rgn mty3 in
    let s = compose_subs s3 (compose_subs s2 s1) in
    let s4 = mgu (apply_m s mty2) (T.TList(mty1, T.THnd(mk_rgn ()))) in
    let s5 = mgu (apply_m s mty3) (T.THnd(r)) in
    let s = compose_subs s5 (compose_subs s4 s) in
    s, T.mk_term (T.Cons(t1', t2', t3')) (generalize env (apply_m s (T.TList(apply_m s mty1, T.THnd(r)))))
  |S.Ref(t1, t2) -> assert false
  |S.Assign(t1, t2) -> assert false
  |S.Deref(t1) -> assert false
  |S.Newrgn -> subs_empty, T.mk_term T.Newrgn (generalize env (T.THnd(mk_rgn ())))
  |S.Aliasrgn(t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer env t2 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let r = get_rgn mty1 in
    let s = compose_subs s1 s2 in
    let s3 = mgu (apply_m s mty1) (T.THnd(r)) in
    let s = compose_subs s s3 in
    s, T.mk_term (T.Aliasrgn(t1', t2')) (generalize env (apply_m s mty2))
  |S.Freergn(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let r = get_rgn mty1 in
    let s2 = mgu (apply_m s1 mty1) (T.THnd(r)) in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Freergn(t1')) (generalize env T.TUnit)
  |S.Sequence(t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer env t2 in
    let mty2 = mty_of (T.get_type t2') in
    let s = compose_subs s1 s2 in
    s, T.mk_term (T.Sequence(t1', t2')) (generalize env (apply_m s mty2))
(*
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
*)

let subs s (T.TPoly(alpha_l, rgn_l, mty)) =
(*Printf.printf ">>>>>>>>> SUBSTITUTION :\n%s\n\n" (strmap_str s (T.show_rcaml_type));*)
(*Printf.printf "subs old mty = %s\n" (T.show_rcaml_type mty);*)
(*  let mty' = apply_m (List.fold_left (fun out a -> StrMap.remove a out) s alpha_l) mty in*)
  let mty' = apply_m s mty in
(*Printf.printf "subs new mty = %s\n" (T.show_rcaml_type mty');*)
  T.TPoly(StrSet.elements (fv_mty mty'), rgn_l, mty')

let subs_iter s ty =
  let rec iter ty old_ty =
(*    Printf.printf "subs %s\n" (T.show_rcaml_type_poly ty);*)
    if ty = old_ty then
      ty
    else
      iter (subs s ty) ty
  in
(*  Printf.printf "subs %s\n" (T.show_rcaml_type_poly ty);*)
  iter (subs s ty) ty

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
      |T.Sequence(t1, t2) -> T.Sequence(subs_term s t1, subs_term s t2)
    )
    (subs_iter s (T.get_type t))

(*
let rec subs_rgn env t =
  let te = T.get_term t in
  let ty = T.get_type t in
  match te with
  |T.Unit |T.Bool(_) |T.Int(_) |T.Var(_) |T.Newrgn -> t
  |T.Binop(op, t1, t2) -> T.mk_term (T.Binop(op, subs_rgn env t1, subs_rgn env t2)) (generalize_rgn env ty)
  |T.Not(t1) -> T.mk_term (T.Not(subs_rgn env t1)) (generalize_rgn env ty)
  |T.Neg(t1) -> T.mk_term (T.Neg(subs_rgn env t1)) (generalize_rgn env ty)
  |T.Comp(c, t1, t2) -> T.mk_term (T.Comp(c, subs_rgn env t1, subs_rgn env t2)) (generalize_rgn env ty)
  |T.Fun(arg_l, t1, t_rgn) ->
    let r = get_rgn (mty_of (T.get_type t_rgn)) in
    T.mk_term (T.Fun(arg_l, 

*)


let type_inference env t =
  let s, t = type_infer env t in
  Printf.printf ">>>>>>>>> SUBSTITUTION :\n%s\n\n" (strmap_str s (T.show_rcaml_type));
  subs_term s t

let type_term t = type_inference StrMap.empty t
