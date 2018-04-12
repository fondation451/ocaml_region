open Util

module S = Region
module T = Check

exception RGN_USED of string

let rec lift_type mty =
  match mty with
  |S.TInt -> T.TInt
  |S.TBool -> T.TBool
  |S.TUnit -> T.TUnit
  |S.TAlpha(a) -> T.TAlpha(a)
  |S.TFun(mty_l, mty1, r) ->
    T.TFun(List.map lift_type mty_l, lift_type mty1, r, T.empty_capabilities, T.empty_capabilities, T.empty_effects)
  |S.TCouple(mty1, mty2, r) -> T.TCouple(lift_type mty1, lift_type mty2, r)
  |S.TList(mty1, r) -> T.TList(lift_type mty1, r)
  |S.TRef(mty1, r) -> T.TRef(lift_type mty1, r)
  |S.THnd(r) -> T.THnd(r)

let fv_mty mty =
  let rec loop mty out =
    match mty with
    |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> out
    |T.TAlpha(a) -> StrSet.add a out
    |T.TFun(mty_l, mty1, r, cin, cout, phie) -> List.fold_left (fun out mty -> loop mty out) (loop mty1 out) mty_l
    |T.TCouple(mty1, mty2, r) -> loop mty1 (loop mty2 out)
    |T.TList(mty1, r) |T.TRef(mty1, r) -> loop mty1 out
  in loop mty StrSet.empty

let fr_mty mty =
  let rec loop mty out =
    match mty with
    |T.TInt |T.TBool |T.TUnit |T.TAlpha(_) -> out
    |T.THnd(r) -> StrSet.add r out
    |T.TFun(mty_l, mty1, r, cin, cout, phie) -> List.fold_left (fun out mty -> loop mty out) (loop mty1 (StrSet.add r out)) mty_l
    |T.TCouple(mty1, mty2, r) -> loop mty1 (loop mty2 (StrSet.add r out))
    |T.TList(mty1, r) |T.TRef(mty1, r) -> loop mty1 (StrSet.add r out)
  in loop mty StrSet.empty

let unrestricted c g = true

let sub_cap c1 c2 = true

let add_rgn r c =
  if StrMap.mem r c then
    StrMap.add r T.Relaxed c
  else
    StrMap.add r T.Linear c

let merge_rgn _ _ _ = Some(T.Relaxed)

let rec rgn_of_mty mty =
  match mty with
  |S.TInt |S.TBool |S.TUnit |S.TAlpha(_) -> StrMap.empty
  |S.TFun(mty_l, mty2, r) ->
    List.fold_left
      (fun out mty1 -> StrMap.union merge_rgn out (rgn_of_mty mty1))
      (add_rgn r (rgn_of_mty mty2))
      mty_l
  |S.TCouple(mty1, mty2, r) -> StrMap.union merge_rgn (rgn_of_mty mty1) (add_rgn r (rgn_of_mty mty2))
  |S.TList(mty1, r) |S.TRef(mty1, r) -> add_rgn r (rgn_of_mty mty1)
  |S.THnd(r) -> StrMap.singleton r T.Linear

let rgn_of_ty (S.TPoly(_, _, mty)) = rgn_of_mty mty

let rec rgn_of t =
  StrMap.union merge_rgn
  (
      match S.get_term t with
      |S.Unit |S.Bool(_) |S.Int(_) |S.Var(_) |S.Newrgn -> StrMap.empty
      |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1) |S.Hd(t1)
      |S.Tl(t1) |S.Nil(t1) |S.Deref(t1) |S.Freergn(t1) ->
        rgn_of t1
      |S.Let(_, t1, t2) |S.Letrec(_, t1, t2) |S.Binop(_, t1, t2) |S.Comp(_, t1, t2)
      |S.Fun(_, t1, t2) |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2) ->
        StrMap.union merge_rgn (rgn_of t1) (rgn_of t2)
      |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) ->
        StrMap.union merge_rgn (rgn_of t1) (StrMap.union merge_rgn (rgn_of t2) (rgn_of t3))
      |S.App(t1, t_l) -> List.fold_left (fun out t2 -> StrMap.union merge_rgn out (rgn_of t2)) (rgn_of t1) t_l
    )
    (rgn_of_ty (S.get_type t))

let subs_empty = StrMap.empty, StrMap.empty

(*
let compose_subs s1 s2 =
  let st1, sr1 = s1 in
  let st2, sr2 = s2 in
  StrMap.union (fun a mty1 mty2 -> mty1

let inst_ty f_ty arg_ty_l =
  match f_ty with
  |T.TPoly(a_l, r_l, T.TFun(mty_l, mty1, mty2, cin, cout, phie)) ->
  |_ -> assert false
*)
let mty_of (T.TPoly(_, _, mty)) = mty

let str_of_cap cap =
  match cap with
  |T.Linear -> "1"
  |T.Relaxed -> "+"
  |T.Used -> "0"

let print_cap c name =
  Printf.printf "%s : \n%s\n"
    name
    ("[" ^ (List.fold_left (fun out (r, cap) -> Printf.sprintf "%s, (%s, %s)" out r (str_of_cap cap)) "" c) ^ "]")

let rec check_term env g c t =
  Printf.printf "--------- CHECK PROCCES ------------\n%s\n\n" (S.show_typed_term t);
  let te = S.get_term t in
  let S.TPoly(a_l, r_l, ty) = S.get_type t in
  match te, ty with
  |S.Unit, S.TUnit -> T.mk_term T.Unit (T.TPoly(a_l, r_l, T.TUnit)), g, c, T.empty_effects
  |S.Bool(b), S.TBool -> T.mk_term (T.Bool(b)) (T.TPoly(a_l, r_l, T.TBool)), g, c, T.empty_effects
  |S.Int(i), S.TInt -> T.mk_term (T.Int(i)) (T.TPoly(a_l, r_l, T.TInt)), g, c, T.empty_effects
  |S.Var(v), _ -> begin
    let ty' = try StrMap.find v env with Not_found -> T.TPoly(a_l, r_l, lift_type ty) in
    let T.TPoly(_, _, mty') = ty' in
    match mty' with
    |T.THnd(r) ->
      if T.cap_linear r c then
        T.mk_term (T.Var(v)) ty', g, T.add_cap r T.Used c, T.effects_of [T.ERead(r)]
      else if T.cap_relaxed r c then
        T.mk_term (T.Var(v)) ty', g, c, T.effects_of [T.ERead(r)]
      else if T.cap_used r c then
        T.mk_term (T.Var(v)) ty', g, T.remove_cap r c, T.effects_of [T.ERead(r)]
      else
        raise (T.Check_Error (Printf.sprintf "No capabilities for region handler %s" r))
    |T.TFun(_, _, r, _, _, _) |T.TCouple(_, _, r) |T.TList(_, r) |T.TRef(_, r) ->
      if T.cap r c then
        T.mk_term (T.Var(v)) ty', g, c, T.effects_of [T.ERead(r)]
      else
        raise (T.Check_Error (Printf.sprintf "No capabilities for access to region %s" r))
    |_ -> T.mk_term (T.Var(v)) ty', g, c, T.empty_effects
  end
  |S.Binop(op, t1, t2), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
    let phi = T.merge_effects phi1 phi2 in
    T.mk_term (T.Binop(op, t1', t2')) (T.TPoly(a_l, r_l, lift_type ty)), g2, c2, phi
  |S.Not(t1), S.TBool ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    T.mk_term (T.Not(t1')) (T.TPoly(a_l, r_l, T.TBool)), g1, c1, phi1
  |S.Neg(t1), S.TInt ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    T.mk_term (T.Neg(t1')) (T.TPoly(a_l, r_l, T.TInt)), g1, c1, phi1
  |S.Comp(comp, t1, t2), S.TBool ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
    let phi = T.merge_effects phi1 phi2 in
    T.mk_term (T.Comp(comp, t1', t2')) (T.TPoly(a_l, r_l, T.TBool)), g2, c2, phi
  |S.Fun(arg_l, t1, t2), S.TFun(mty_l, mty1, r) ->
    let t2', g2, c2, phi2 = check_term env g c t2 in
    let env' =
      List.fold_left2
        (fun out x mty ->
          let mty' = lift_type mty in
          let a_l' = StrSet.elements (fv_mty mty') in
          let r_l' = StrSet.elements (StrSet.inter (fr_mty mty') (StrSet.of_list r_l)) in
          StrMap.add x (T.TPoly(a_l', r_l', mty')) out)
      env arg_l mty_l
    in
    let cin = T.cap_of_strmap (rgn_of t1) in
    print_cap cin "cin";
    let t1', g1, cout, phi_f = check_term env' g2 cin t1 in
    print_cap cout "cout";
    let cin' = T.diff_cap cin (T.cap_of r_l) in
    print_cap cin' "cin'";
    let cout' = T.diff_cap cout (T.cap_of r_l) in
    print_cap cout' "cout'";
    if T.cap r c2 && g2 = g1 && unrestricted cin g2 then
      T.mk_term
        (T.Fun(arg_l, t1', t2'))
        (T.TPoly(a_l, r_l, T.TFun(List.map lift_type mty_l, lift_type mty1, r, cin, cout, phi_f))),
      g2, c2, T.merge_effects (T.effects_of [T.EAlloc(r)]) phi2
    else
      raise (T.Check_Error (Printf.sprintf "Error with function region behaviour %s" r))
  |S.App(t1, t_l), _ -> begin
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t_l', g2, c2, phi2 =
      let rec loop g c t_l =
        match t_l with
        |[] -> [], g, c, T.empty_effects
        |head::tail ->
          let head', g', c', phi' = check_term env g c head in
          let t_l_out, g_out, c_out, phi_out = loop g' c' tail in
          head'::t_l_out, g_out, c_out, T.merge_effects phi' phi_out
      in loop g1 c1 t_l
    in
    match T.get_type t1' with
    |T.TPoly(a_l_f, r_l_f, T.TFun(arg_mty_l, mty_res, mty_r, cin, cout, phie)) as f_ty ->
(*      let new_f_ty = inst_ty f_ty (List.map T.get_type t_l') in*)
      if sub_cap c2 cin then
        T.mk_term (T.App(t1', t_l')) (T.TPoly(a_l, r_l, lift_type ty)),
        g2,
        T.union_cap (T.diff_cap c2 (T.diff_cap cin cout)) (T.diff_cap cout cin),
        T.merge_effects phie (T.merge_effects phi1 phi2)
      else
        raise (T.Check_Error (Printf.sprintf "Function call : capabilities not sub cap of cin"))
    |_ -> assert false
  end
  |S.If(t1, t2, t3), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
    let t3', g3, c3, phi3 = check_term env g2 c2 t3 in
    T.mk_term (T.If(t1', t2', t3')) (T.TPoly(a_l, r_l, lift_type ty)), g3, c3, T.merge_effects phi1 (T.merge_effects phi2 phi3)
  |S.Let(x, t1, t2), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term (StrMap.add x (T.get_type t1') env) g1 c1 t2 in
    T.mk_term (T.Let(x, t1', t2')) (T.TPoly(a_l, r_l, lift_type ty)), g2, c2, T.merge_effects phi1 phi2
  |S.Letrec(x, t1, t2), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let env' = StrMap.add x (T.get_type t1') env in
    let t1', g1, c1, phi1 = check_term env' g c t1 in
    let t2', g2, c2, phi2 = check_term env' g1 c1 t2 in
    T.mk_term (T.Letrec(x, t1', t2')) (T.TPoly(a_l, r_l, lift_type ty)), g2, c2, T.merge_effects phi1 phi2
  |S.Pair(t1, t2, t3), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
    let t3', g3, c3, phi3 = check_term env g2 c2 t3 in
    let phi = T.merge_effects phi1 (T.merge_effects phi2 phi3) in
    T.mk_term (T.Pair(t1', t2', t3')) (T.TPoly(a_l, r_l, lift_type ty)), g3, c3, phi
  |S.Fst(t1), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    T.mk_term (T.Fst(t1')) (T.TPoly(a_l, r_l, lift_type ty)), g1, c1, phi1
  |S.Snd(t1), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    T.mk_term (T.Snd(t1')) (T.TPoly(a_l, r_l, lift_type ty)), g1, c1, phi1
  |S.Hd(t1), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    T.mk_term (T.Hd(t1')) (T.TPoly(a_l, r_l, lift_type ty)), g1, c1, phi1
  |S.Tl(t1), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    T.mk_term (T.Tl(t1')) (T.TPoly(a_l, r_l, lift_type ty)), g1, c1, phi1
  |S.Nil(t1), S.TList(_, r) ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    T.mk_term (T.Nil(t1')) (T.TPoly(a_l, r_l, lift_type ty)), g1, c1, phi1
  |S.Cons(t1, t2, t3), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
    let t3', g3, c3, phi3 = check_term env g2 c2 t3 in
    let phi = T.merge_effects phi1 (T.merge_effects phi2 phi3) in
    T.mk_term (T.Cons(t1', t2', t3')) (T.TPoly(a_l, r_l, lift_type ty)), g3, c3, phi
  |S.Ref(t1, t2), _ -> assert false
  |S.Assign(t1, t2), _ -> assert false
  |S.Deref(t1), _ -> assert false
  |S.Newrgn, S.THnd(r) -> T.mk_term T.Newrgn (T.TPoly(a_l, r_l, T.THnd(r))), g, T.add_cap r T.Linear c, T.empty_effects
  |S.Aliasrgn(t1, t2), _ -> begin
    let t1', g1, c1, phi1 = check_term env g c t1 in
    print_cap c "c";
    print_cap c1 "c1";
    match T.get_type t1' with
    |T.TPoly(_, _, T.THnd(r)) ->
      if T.cap_used r c1 then
        let t2', g2, c2, phi2 = check_term env g (T.add_cap r T.Relaxed c1) t2 in
        T.mk_term (T.Aliasrgn(t1', t2')) (T.TPoly(a_l, r_l, lift_type ty)), g2, T.add_cap r T.Linear c2, T.merge_effects phi1 phi2
      else
        raise (T.Check_Error (Printf.sprintf "capability of %s not in c1" r))
    |_ -> assert false
  end
  |S.Freergn(t1), S.TUnit -> begin
      let t1', g1, c1, phi1 = check_term env g c t1 in
      match T.get_type t1' with
      |T.TPoly(_, _, T.THnd(r)) when not (T.cap_relaxed r c1) ->
        T.mk_term (T.Freergn(t1')) (T.TPoly(a_l, r_l, T.TUnit)), g1, T.remove_cap r c1, phi1
      |_ -> assert false
  end
  |S.Sequence(t1, t2), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
    T.mk_term (T.Sequence(t1', t2')) (T.TPoly(a_l, r_l, lift_type ty)), g2, c2, T.merge_effects phi1 phi2
  |_ -> assert false

let rgn_check t =
  try
    let t', _, _, _ = check_term StrMap.empty T.empty_gamma T.empty_capabilities t in
    t'
  with
  |RGN_USED(r) -> raise (T.Check_Error (Printf.sprintf "Capability of region %s already used" r))
  |T.Check_Error(str) -> raise (T.Check_Error str)
