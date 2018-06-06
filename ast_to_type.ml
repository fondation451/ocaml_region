open Util

module S = Ast
module T = Type

(* ALGORITHM W *)

let str_of_subs s =
  let st, sr = s in
  Printf.sprintf "%s\n%s" (strmap_str st T.show_rcaml_type) (strmap_str sr T.show_regions)

let fv_mty mty =
  let rec loop mty out =
    match mty with
    |T.TAlpha(a) -> StrSet.add a out
    |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> out
    |T.TFun(mty_l, mty2, _) -> List.fold_left (fun out mty -> loop mty out) (loop mty2 out) mty_l
    |T.TCouple(mty1, mty2, _) -> loop mty1 (loop mty2 out)
    |T.TList(_, mty1, _) -> loop mty1 out
    |T.TRef(_, mty1, _) -> loop mty1 out
  in loop mty StrSet.empty

let fv_ty (T.TPoly(alpha_l, _, mty)) = StrSet.diff (fv_mty mty) (StrSet.of_list alpha_l)

let fv_ty_l ty_l = List.fold_left (fun out ty -> StrSet.union (fv_ty ty) out) StrSet.empty ty_l

let fr_r r out=
  match r with
  |T.RRgn(_) -> StrSet.empty
  |T.RAlpha(rgn) -> StrSet.singleton rgn

let fr_mty mty =
  let fr_r r out =
    match r with
    |T.RRgn(_) -> out
    |T.RAlpha(rgn) -> StrSet.add rgn out
  in
  let rec loop mty out =
    match mty with
    |T.TAlpha(_) |T.TInt |T.TBool |T.TUnit -> out
    |T.THnd(r) -> fr_r r out
    |T.TFun(mty_l, mty2, r) ->
      List.fold_left (fun out mty -> loop mty out) (loop mty2 (fr_r r out)) mty_l
    |T.TCouple(mty1, mty2, r) -> loop mty1 (loop mty2 (fr_r r out))
    |T.TList(_, mty1, r) |T.TRef(_, mty1, r) -> loop mty1 (fr_r r out)
  in loop mty StrSet.empty

let fr_ty (T.TPoly(_, rgn_l, mty)) = StrSet.diff (fr_mty mty) (StrSet.of_list rgn_l)

let fr_ty_l ty_l = List.fold_left (fun out ty -> StrSet.union (fr_ty ty) out) StrSet.empty ty_l

let apply_r sr r =
  match r with
  |T.RRgn(_) -> r
  |T.RAlpha(rgn) -> (try StrMap.find rgn sr with Not_found -> r)

let rec apply_m s mty =
  let st, sr = s in
  match mty with
  |T.TAlpha(a) -> (try StrMap.find a st with Not_found -> T.TAlpha(a))
  |T.TInt |T.TBool |T.TUnit -> mty
  |T.THnd(r) -> T.THnd(apply_r sr r)
  |T.TFun(mty_l, mty2, r) ->
    T.TFun(List.map (fun mty -> apply_m s mty) mty_l, apply_m s mty2, apply_r sr r)
  |T.TCouple(mty1, mty2, r) -> T.TCouple(apply_m s mty1, apply_m s mty2, apply_r sr r)
  |T.TList(ls, mty1, r) -> T.TList(ls, apply_m s mty1, apply_r sr r)
  |T.TRef(id, mty1, r) -> T.TRef(id, apply_m s mty1, apply_r sr r)

let remove_subs alpha_l rgn_l s =
  let st, sr = s in
  List.fold_left (fun out a -> StrMap.remove a out) st alpha_l,
  List.fold_left (fun out r -> StrMap.remove r out) sr rgn_l

let apply s (T.TPoly(alpha_l, rgn_l, mty)) =
  T.TPoly(alpha_l, rgn_l, apply_m (remove_subs alpha_l [] s) mty)

let subs_empty = StrMap.empty, StrMap.empty

let subs_of_rsubs sr = StrMap.empty, sr

let remove_env env var = StrMap.remove var env

let fv_env env = fv_ty_l (List.rev_map snd (StrMap.bindings env))

let fr_env env = fr_ty_l (List.rev_map snd (StrMap.bindings env))

let apply_env s env = StrMap.map (apply s) env

let generalize env mty =
  T.TPoly(
    StrSet.elements (StrSet.diff (fv_mty mty) (fv_env env)),
    StrSet.elements (StrSet.diff (fr_mty mty) (fr_env env)),
    mty
  )

let instanciate (T.TPoly(alpha_l, rgn_l, mty)) =
  let alpha_l_ty = List.map (fun _ -> T.TAlpha(mk_var ())) alpha_l in
  let rgn_l_r = List.map (fun _ -> T.RAlpha(mk_rgn ())) rgn_l in
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
  apply_m s mty

let varbind alpha mty =
  match mty with
  |T.TAlpha(alpha') when alpha = alpha' -> subs_empty
  |_ ->
    if StrSet.mem alpha (fv_mty mty) then
      raise (T.Error(Printf.sprintf "Varbind : %s occurs in %s      %s"
                                    alpha
                                    (T.show_rcaml_type mty)
                                    (strset_str (fv_mty mty))))
    else
      StrMap.singleton alpha mty, StrMap.empty

let rgnbind r1 r2 =
  match r1, r2 with
  |T.RRgn(rgn1), T.RRgn(rgn2) ->
    if rgn1 = rgn2 then
      subs_empty
    else
      raise (T.Error "rgnbind")
  |T.RAlpha(rgn1), T.RRgn(rgn2) -> StrMap.empty, StrMap.singleton rgn1 r2
  |T.RRgn(rgn1), T.RAlpha(rgn2) -> StrMap.empty, StrMap.singleton rgn2 r1
  |T.RAlpha(rgn1), T.RAlpha(rgn2) ->
    if rgn1 = rgn2 then
      subs_empty
    else
      StrMap.empty, StrMap.singleton rgn1 r2

let rec mgu mty1 mty2 =
  match mty1, mty2 with
  |T.TInt, T.TInt |T.TBool, T.TBool |T.TUnit, T.TUnit -> subs_empty
  |T.THnd(r1), T.THnd(r2) -> rgnbind r1 r2
  |T.TAlpha(a1), _ -> varbind a1 mty2
  |_, T.TAlpha(a2) -> varbind a2 mty1
  |T.TFun(arg_l1, dst1, r1), T.TFun(arg_l2, dst2, r2) -> begin
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
      raise (T.Error ("Unification of Functions, different number of arguments : " ^ str))
  end
  |T.TCouple(mty1, mty2, r), T.TCouple(mty1', mty2', r') ->
    let s1 = mgu mty1 mty1' in
    let s2 = mgu (apply_m s1 mty2) (apply_m s1 mty2') in
    let s3 = rgnbind r r' in
    compose_subs s3 (compose_subs s1 s2)
  |T.TList(_, mty1, r), T.TList(_, mty1', r') |T.TRef(_, mty1, r), T.TRef(_, mty1', r') ->
    let s1 = mgu mty1 mty1' in
    let s2 = rgnbind r r' in
    compose_subs s1 s2
  |_ -> raise (T.Error(Printf.sprintf "Mgu %s %s" (T.show_rcaml_type mty1) (T.show_rcaml_type mty2)))

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
      (* Printf.printf "\n\ncompose subs %s : %s %s -> %s\n%s\n\n" k (T.show_rcaml_type mty1) (T.show_rcaml_type mty2) (T.show_rcaml_type out) (str_of_subs s); *)
      Some(out)) (StrMap.map (apply_m s1) st2) st1 in
  let sr = StrMap.union
    (fun r rgn1 rgn2 ->
      let s = mgu (T.THnd(rgn1)) (T.THnd(rgn2)) in
      let st, sr = s in
      acc_s := compose_subs s !acc_s;
      let out = apply_r sr rgn1 in
      (* Printf.printf "\n\ncompose subs %s : %s %s -> %s\n%s\n\n" r (T.show_regions rgn1) (T.show_regions rgn2) (T.show_regions out) (str_of_subs s); *)
      Some(rgn1))
    (StrMap.map (apply_r sr1) sr2) sr1 in
  compose_subs !acc_s (st, sr)
)

let remove_env env var = StrMap.remove var env

let mty_of (T.TPoly(_, _, mty)) = mty

let get_rgn mty =
  match mty with
  |T.THnd(r) -> r
  |_ -> T.RRgn(mk_rgn ())

(***********)

let rec type_infer env t =
  (* Printf.printf "--------- TYPING PROCCES ------------\n%s\n\n" (S.show_term t); *)
  match t with
  |S.Var(var) -> begin
    try
Printf.printf "@@@@@@@@@@ VAR %s ENV\n%s\n\n" var (strmap_str env T.show_rcaml_type_poly);
      subs_empty, T.mk_term (T.Var(var)) (generalize env (instanciate (StrMap.find var env)))
    with Not_found -> raise (T.Error "Type_infer")
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
    let s = compose_subs s4 (compose_subs s3 (compose_subs s2 s1)) in
    s, T.mk_term (T.Binop(op, t1', t2')) (generalize env T.TInt)
  |S.Not(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s2 = mgu (apply_m s1 mty1) T.TBool in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Not(t1')) (generalize env T.TBool)
  |S.Neg(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s2 = mgu (apply_m s1 mty1) T.TInt in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Neg(t1')) (generalize env T.TInt)
  |S.Comp(c, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer (apply_env s1 env) t2 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let s = compose_subs s2 s1 in
    let s =
      match c with
      |T.Ceq |T.Cneq ->
        let s3 = mgu (apply_m s mty1) (apply_m s mty2) in
        compose_subs s3 s
      |_ ->
        let s3 = mgu (apply_m s1 mty1) T.TInt in
        let s4 = mgu (apply_m s2 mty2) T.TInt in
        compose_subs s4 (compose_subs s3 s)
    in
    s, T.mk_term (T.Comp(c, t1', t2')) (generalize env T.TBool)
  |S.Fun(f, x_l, t1, t2, pot) ->
    let a_l = List.rev_map (fun _ -> T.TAlpha(mk_var ())) x_l in
    let env' =
      List.fold_left2
        (fun env x mty -> StrMap.add x (T.TPoly([], [], mty)) env)
        env x_l a_l
    in
    let s1, t1' = type_infer env' t1 in
    let s2, t2' = type_infer (apply_env s1 env') t2 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let r = T.RAlpha(mk_rgn ()) in
    let s3 = mgu (apply_m s2 mty2) (T.THnd(r)) in
    let s = compose_subs s3 (compose_subs s2 s1) in
    s, T.mk_term
         (T.Fun(f, x_l, t1', t2', pot))
         (generalize env (T.TFun(List.map (fun mty -> apply_m s mty) a_l,
                                 apply_m s mty1,
                                 apply_r (snd s) r)))
  |S.App(t1, t2_l) ->
    let mty = T.TAlpha(mk_var ()) in
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s2, t2_l' =
      List.fold_left
        (fun (s, t_l) t ->
          let tmp_s, tmp_t = type_infer (apply_env s env) t in
          compose_subs tmp_s s, tmp_t::t_l)
        (subs_empty, [])
        t2_l
    in
    let t2_l' = List.rev t2_l' in
    let ty_t2_l = List.map (fun t -> mty_of (T.get_type t)) t2_l' in
    let s3 = mgu (apply_m s2 mty1) (T.TFun(ty_t2_l, mty, T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s3 (compose_subs s2 s1) in
    s, T.mk_term (T.App(t1', t2_l')) (generalize env (apply_m s mty))
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
    (* Printf.printf "((((((((((((((((((( IF TYPAGE DES BRANCHES TERMINE !!!!\n\n"; *)
    let s4 = mgu (apply_m s2 mty2) (apply_m s3 mty3) in
    let s = compose_subs s4 (compose_subs s3 (compose_subs s2 (compose_subs s1' s1))) in
    s, T.mk_term (T.If(t1', t2', t3')) (generalize env (apply_m s mty2))
  |S.Match(t_match, t_nil, x, xs, t_cons) ->
    let s1, t_match' = type_infer env t_match in
    let mty_match = mty_of (T.get_type t_match') in
    let a1 = T.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty_match) (T.TList(None, a1, T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s1 s2 in
    let env = apply_env s env in
    let s3, t_nil' = type_infer env t_nil in
    let env = apply_env s3 env in
    let env' =
      StrMap.add
        x
        (T.TPoly([], [], apply_m s a1))
        (StrMap.add xs (T.TPoly([], [], T.TList(None, apply_m s a1, T.RAlpha(mk_rgn ())))) env)
    in
    let s4, t_cons' = type_infer env' t_cons in
    let mty_nil = mty_of (T.get_type t_nil') in
    let mty_cons = mty_of (T.get_type t_cons') in
    let s = compose_subs s4 (compose_subs s3 s) in
    let s5 = mgu (apply_m s mty_nil) (apply_m s mty_cons) in
    let s = compose_subs s5 s in
    s, T.mk_term (T.Match(t_match', t_nil', x, xs, t_cons')) (generalize env (apply_m s mty_cons))
  |S.Let(x, t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let env' = StrMap.add x (generalize (apply_env s1 env) mty1) env in
    let s2, t2' = type_infer (apply_env s1 env') t2 in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Let(x, t1', t2')) (T.get_type t2')
  |S.Letrec(f, t1, t2) ->
    let a = T.TAlpha(mk_var ()) in
    let env' = StrMap.add f (T.TPoly([], [], a)) env in
    let s1, t1' = type_infer env' t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s1' = mgu (apply_m s1 a) (apply_m s1 mty1) in
    let s = compose_subs s1' s1 in
    let env'' = StrMap.add f (generalize (apply_env s env) (apply_m s mty1)) env' in
    let s2, t2' = type_infer (apply_env s env'') t2 in
    let s = compose_subs s2 s in
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
    let r = T.RAlpha(mk_rgn ()) in
    let s = compose_subs s3 (compose_subs s2 s1) in
    let s4 = mgu (apply_m s mty3) (T.THnd(r)) in
    let s = compose_subs s4 s in
    s, T.mk_term (T.Pair(t1', t2', t3')) (generalize env (T.TCouple(mty1, mty2, r)))
  |S.Fst(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let a1 = T.TAlpha(mk_var ()) in
    let a2 = T.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (T.TCouple(a1, a2, T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Fst(t1')) (generalize env (apply_m s a1))
  |S.Snd(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let a1 = T.TAlpha(mk_var ()) in
    let a2 = T.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (T.TCouple(a1, a2, T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Snd(t1')) (generalize env (apply_m s a2))
  |S.Hd(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let tmp = mk_var () in
    let a1 = T.TAlpha(tmp) in
    let s2 = mgu (apply_m s1 mty1) (T.TList(None, a1, T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
  let st, sr = s in
  (* Printf.printf "\n\n\n&&&&&&&&&&&&& HD SUB (%s) :\n%s\n\nSUBSTITUTION RGN :\n%s\n\n" tmp (strmap_str st T.show_rcaml_type) (strmap_str sr T.show_regions); *)
    s, T.mk_term (T.Hd(t1')) (generalize env a1)
  |S.Tl(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let a1 = T.TAlpha(mk_var ()) in
    let s2 = mgu (apply_m s1 mty1) (T.TList(None, a1, T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Tl(t1')) (generalize env (apply_m s mty1))
  |S.Nil ->
    subs_empty, T.mk_term T.Nil (generalize env (T.TList(None,
                                                         T.TAlpha(mk_var ()),
                                                         T.RAlpha(mk_rgn ()))))
  |S.Cons(t1, t2, t3) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env  = apply_env s2 env in
    let s3, t3' = type_infer env t3 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let mty3 = mty_of (T.get_type t3') in
    let r = T.RAlpha(mk_rgn ()) in
    let s = compose_subs s3 (compose_subs s2 s1) in
    let s4 = mgu (apply_m s mty2) (T.TList(None, apply_m s mty1, T.RAlpha(mk_rgn ()))) in
    let s5 = mgu (apply_m s mty3) (T.THnd(r)) in
    let s = compose_subs s5 (compose_subs s4 s) in
    s, T.mk_term (T.Cons(t1', t2', t3'))
                 (generalize env (apply_m s (T.TList(None, apply_m s mty1, r))))
  |S.Ref(t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env  = apply_env s2 env in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let r = T.RAlpha(mk_rgn ()) in
    let s = compose_subs s2 s1 in
    let s3 = mgu (apply_m s mty2) (T.THnd(r)) in
    let s = compose_subs s3 s in
    s, T.mk_term (T.Ref(t1', t2')) (generalize env (apply_m s (T.TRef(0, apply_m s mty1, r))))
  |S.Assign(t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let env = apply_env s1 env in
    let s2, t2' = type_infer env t2 in
    let env  = apply_env s2 env in
    let s = compose_subs s2 s1 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let r = T.RAlpha(mk_rgn ()) in
    Printf.printf "Assign : %s\n" (T.show_regions r);
    let s3 = mgu (T.TRef(0, apply_m s mty2, r)) (apply_m s mty1) in
    let s = compose_subs s3 s in
    s, T.mk_term (T.Assign(t1', t2')) (generalize env T.TUnit)
  |S.Deref(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let tmp = mk_var () in
    let a1 = T.TAlpha(tmp) in
    let s2 = mgu (apply_m s1 mty1) (T.TRef(0, a1, T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Deref(t1')) (generalize env a1)
  |S.Newrgn -> subs_empty, T.mk_term T.Newrgn (generalize env (T.THnd(T.RRgn(mk_rgn ()))))
  |S.Aliasrgn(t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer env t2 in
    let mty1 = mty_of (T.get_type t1') in
    let mty2 = mty_of (T.get_type t2') in
    let s = compose_subs s2 s1 in
    let s3 = mgu (apply_m s mty1) (T.THnd(T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s3 s in
    s, T.mk_term (T.Aliasrgn(t1', t2')) (generalize env (apply_m s mty2))
  |S.Freergn(t1) ->
    let s1, t1' = type_infer env t1 in
    let mty1 = mty_of (T.get_type t1') in
    let s2 = mgu (apply_m s1 mty1) (T.THnd(T.RAlpha(mk_rgn ()))) in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Freergn(t1')) (generalize env T.TUnit)
  |S.Sequence(t1, t2) ->
    let s1, t1' = type_infer env t1 in
    let s2, t2' = type_infer env t2 in
    let mty2 = mty_of (T.get_type t2') in
    let s = compose_subs s2 s1 in
    s, T.mk_term (T.Sequence(t1', t2')) (generalize env (apply_m s mty2))

let normalize_ty (T.TPoly(_, _, mty)) =
  T.TPoly(StrSet.elements (fv_mty mty), StrSet.elements (fr_mty mty), mty)

let iter_fun f x =
  let rec loop x old = if x = old then x else loop (f x) x in
  loop (f x) x

let force_subs s (T.TPoly(alpha_l, rgn_l, mty)) =
  T.TPoly(alpha_l, rgn_l, apply_m s mty)

let rec subs_term s t =
  T.mk_term
    (
      match T.get_term t with
      |T.Unit |T.Bool(_) |T.Int(_) |T.Var(_) |T.Newrgn -> T.get_term t
      |T.Binop(op, t1, t2) -> T.Binop(op, subs_term s t1, subs_term s t2)
      |T.Not(t1) -> T.Not(subs_term s t1)
      |T.Neg(t1) -> T.Neg(subs_term s t1)
      |T.Comp(c, t1, t2) -> T.Comp(c, subs_term s t1, subs_term s t2)
      |T.Fun(f, arg_l, t1, t2, pot) -> T.Fun(f, arg_l, subs_term s t1, subs_term s t2, pot)
      |T.App(t1, t_l) -> T.App(subs_term s t1, List.map (subs_term s) t_l)
      |T.If(t1, t2, t3) -> T.If(subs_term s t1, subs_term s t2, subs_term s t3)
      |T.Match(t_match, t_nil, x, xs, t_cons) ->
        T.Match(subs_term s t_match, subs_term s t_nil, x, xs, subs_term s t_cons)
      |T.Let(x, t1, t2) -> T.Let(x, subs_term s t1, subs_term s t2)
      |T.Letrec(f, t1, t2) -> T.Letrec(f, subs_term s t1, subs_term s t2)
      |T.Pair(t1, t2, t3) -> T.Pair(subs_term s t1, subs_term s t2, subs_term s t3)
      |T.Fst(t1) -> T.Fst(subs_term s t1)
      |T.Snd(t1) -> T.Snd(subs_term s t1)
      |T.Hd(t1) -> T.Hd(subs_term s t1)
      |T.Tl(t1) -> T.Tl(subs_term s t1)
      |T.Nil -> T.Nil
      |T.Cons(t1, t2, t3) -> T.Cons(subs_term s t1, subs_term s t2, subs_term s t3)
      |T.Ref(t1, t2) -> T.Ref(subs_term s t1, subs_term s t2)
      |T.Assign(t1, t2) -> T.Assign(subs_term s t1, subs_term s t2)
      |T.Deref(t1) -> T.Deref(subs_term s t1)
      |T.Aliasrgn(t1, t2) -> T.Aliasrgn(subs_term s t1, subs_term s t2)
      |T.Freergn(t1) -> T.Freergn(subs_term s t1)
      |T.Sequence(t1, t2) -> T.Sequence(subs_term s t1, subs_term s t2)
    )
    (normalize_ty (iter_fun (force_subs s) (T.get_type t)))

let type_inference env t =
  let s, t = type_infer env t in
  let st, sr = s in
  Printf.printf "SUBSTITUTION TYPE :\n%s\n\nSUBSTITUTION RGN :\n%s\n\n" (strmap_str st T.show_rcaml_type) (strmap_str sr T.show_regions);
  subs_term s t

let process t = type_inference StrMap.empty t
