open Util

module S = Region
module T = Check

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

let unrestricted c g = true (* TODO *)

let sub_cap c1 c2 =
  T.cap_forall
(*    (fun (r, p) ->
      (p = T.Relaxed && (T.cap_linear r c1 || T.cap_relaxed r c1)) ||
      (p = T.Linear && T.cap_linear r c1)) *)
    (fun (r, p) ->
      (p = T.Relaxed && T.cap_relaxed r c1) ||
      (p = T.Linear && (T.cap_linear r c1 || T.cap_relaxed r c1)) ||
      (p = T.Used && T.cap r c1))
    c2

(* Construction CIN *)
let sum_rgn_p p1 p2 =
  match p1, p2 with
  |T.Used, _ -> p2
  |_, T.Used -> p1
  |_ -> T.Relaxed

let add_rgn r p c =
  StrMap.add r (try sum_rgn_p (StrMap.find r c) p with Not_found -> p) c

let merge_rgn _ _ _ = Some(T.Relaxed)

let rec rgn_of_mty mty =
  match mty with
  |S.TInt |S.TBool |S.TUnit |S.TAlpha(_) -> StrMap.empty
  |S.TFun(mty_l, mty2, r) ->
    List.fold_left
      (fun out mty1 -> StrMap.union merge_rgn out (rgn_of_mty mty1))
      (add_rgn r T.Used (rgn_of_mty mty2))
      mty_l
  |S.TCouple(mty1, mty2, r) -> StrMap.union merge_rgn (rgn_of_mty mty1) (add_rgn r T.Used (rgn_of_mty mty2))
  |S.TList(mty1, r) |S.TRef(mty1, r) -> add_rgn r T.Used (rgn_of_mty mty1)
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
      |S.Fun(_, _, t1, t2, _) |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2) ->
        StrMap.union merge_rgn (rgn_of t1) (rgn_of t2)
      |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) |S.Match(t1, t2, _, _, t3) ->
        StrMap.union merge_rgn (rgn_of t1) (StrMap.union merge_rgn (rgn_of t2) (rgn_of t3))
      |S.App(t1, t_l) -> List.fold_left (fun out t2 -> StrMap.union merge_rgn out (rgn_of t2)) (rgn_of t1) t_l
    )
    (rgn_of_ty (S.get_type t))
(* **** *)


(* Instanciation of regions in application *)
let merge_some s1 s2 =
  match s1, s2 with
  |None, None -> None
  |Some(out), None |None, Some(out) -> Some(out)
  |Some(out1), Some(out2) -> if out1 = out2 then Some(out1) else assert false

let rec replace_rgn s mty =
  let replace s r = try StrMap.find r s with Not_found -> r in
  let replace_cap s c = T.cap_map (fun (r, p) -> (replace s r, p)) c in
  let replace_effects s phi =
    T.effects_map
      (fun e ->
        match e with
        |T.ERead(r) -> T.ERead(replace s r)
        |T.EWrite(r) -> T.EWrite(replace s r)
        |T.EAlloc(r) -> T.EAlloc(replace s r))
      phi
  in
  match mty with
  |T.TInt|T.TBool |T.TUnit |T.TAlpha(_) -> mty
  |T.THnd(r) -> T.THnd(replace s r)
  |T.TFun(arg_l, mty1, r, cin, cout, phie) ->
    T.TFun
      (
        List.map (replace_rgn s) arg_l,
        replace_rgn s mty1,
        replace s r,
        replace_cap s cin,
        replace_cap s cout,
        replace_effects s phie
      )
  |T.TCouple(mty1, mty2, r) -> T.TCouple(replace_rgn s mty1, replace_rgn s mty2, replace s r)
  |T.TList(mty1, r) -> T.TList(replace_rgn s mty1, replace s r)
  |T.TRef(mty1, r) -> T.TRef(replace_rgn s mty1, replace s r)

let rec replace_rgn_ty s (T.TPoly(_, _, mty)) = replace_rgn s mty

let rec instance_of_rgn r mty1 mty2 =
  match mty1, mty2 with
  |T.TInt, T.TInt |T.TBool, T.TBool |T.TUnit, T.TUnit |T.TAlpha(_), T.TAlpha(_) |T.TAlpha(_), _ |_, T.TAlpha(_) -> None
  |T.THnd(r1), T.THnd(r2) ->
    if r1 = r then
      Some(r2)
    else
      None
  |T.TFun(arg_l1, dst1, r1, _, _, _), T.TFun(arg_l2, dst2, r2, _, _, _) ->
    if r1 = r then
      Some(r2)
    else
      List.fold_left2
        (fun out arg1 arg2 -> merge_some (instance_of_rgn r arg1 arg2) out)
        (instance_of_rgn r dst1 dst2)
        arg_l1
        arg_l2
  |T.TCouple(mty1, mty2, r1), T.TCouple(mty1', mty2', r2) ->
    if r1 = r then
      Some(r2)
    else
      merge_some (instance_of_rgn r mty1 mty1') (instance_of_rgn r mty2 mty2')
  |T.TList(mty1, r1), T.TList(mty1', r2) |T.TRef(mty1, r1), T.TRef(mty1', r2) ->
    if r = r1 then
      Some(r2)
    else
      instance_of_rgn r mty1 mty1'
  |_ -> raise (T.Check_Error(Printf.sprintf "instance_of_rgn %s %s %s" r (T.show_rcaml_type mty1) (T.show_rcaml_type mty2)))

let instance_of_rgn_l r_l mty1 mty2 =
  let s = List.fold_left
            (fun out r ->
              match instance_of_rgn r mty1 mty2 with
              |Some(r') -> StrMap.add r r' out
              |None -> out)
            StrMap.empty r_l
  in
  let r_proceed = List.map fst (StrMap.bindings s) in
  List.filter (fun r -> not (List.mem r r_proceed)) r_l, s

let rec instance_of_rgn_mty_l r_l mty1_l mty2_l =
  let rec loop r_l mty1_l mty2_l out =
    if r_l = [] then
      [], out
    else begin
      match mty1_l, mty2_l with
      |[], [] -> r_l, out
      |mty1::mty1_l', mty2::mty2_l' ->
        let r_l', s = instance_of_rgn_l r_l mty1 mty2 in
        loop r_l' mty1_l' mty2_l' (StrMap.union (fun _ r1 r2 -> Some(r1)) s out)
      |_ -> assert false
    end
  in loop r_l mty1_l mty2_l StrMap.empty

let inst_ty f_ty arg_ty_l =
  match f_ty with
  |T.TPoly(a_l, r_l, T.TFun(mty_l, mty1, mty2, cin, cout, phie)) ->
    let r_l', s = instance_of_rgn_mty_l r_l mty_l arg_ty_l in
    a_l, r_l', s
  |_ -> assert false
(* **** *)


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
(*  Printf.printf "--------- CHECK PROCCES ------------\n%s\n\n" (S.show_typed_term t);*)
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
  |S.Fun(f, arg_l, t1, t2, pot), S.TFun(mty_l, mty1, r) ->
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
        (T.Fun(f, arg_l, t1', t2', pot))
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
    let a_l', r_l', s = inst_ty (T.get_type t1') (List.map (fun t -> mty_of (T.get_type t)) t_l') in
    let s' = StrMap.bindings s in
    let t1_ty'' = replace_rgn_ty s (T.get_type t1') in
    let t1'' = T.mk_term (T.get_term t1') (T.TPoly(a_l', r_l', t1_ty'')) in
    Printf.printf "AAAAAAAAAAAAAAAQQQQQQQQQQQQQQQQUUUUUUUUUUUUUUUUUIIIIIIIIIIIIIIIII %s\n\n\n\n\n" (T.show_rcaml_type t1_ty'');
    match T.get_type t1'' with
    |T.TPoly(a_l_f, r_l_f, T.TFun(arg_mty_l, mty_res, mty_r, cin, cout, phie)) as f_ty ->
      Printf.printf "C2 : %s\n\n" (T.show_capabilities c2);
(*      let new_f_ty = inst_ty f_ty (List.map T.get_type t_l') in*)
      if sub_cap c2 cin then
        T.mk_term (T.App(s', t1'', t_l')) (T.TPoly(a_l, r_l, lift_type ty)),
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
  |S.Match(t_match, t_nil, x, xs, t_cons), _ ->
    let t_match', g1, c1, phi1 = check_term env g c t_match in
    let t_nil', g2, c2, phi2 = check_term env g1 c1 t_nil in
    let t_cons', g3, c3, phi3 = check_term env g2 c2 t_cons in
    T.mk_term
      (T.Match(t_match', t_nil', x, xs, t_cons'))
      (T.TPoly(a_l, r_l, lift_type ty)),
    g3,
    c3,
    T.merge_effects phi1 (T.merge_effects phi2 phi3)
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
  |S.Ref(t1, t2), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
    let phi = T.merge_effects phi1 phi2 in
    T.mk_term (T.Ref(t1', t2')) (T.TPoly(a_l, r_l, lift_type ty)), g2, c2, phi
  |S.Assign(t1, t2), S.TRef(_, r) ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
    let phi = T.merge_effects (T.effects_of [T.EWrite(r)]) (T.merge_effects phi1 phi2) in
    T.mk_term (T.Assign(t1', t2')) (T.TPoly(a_l, r_l, lift_type ty)), g2, c2, phi
  |S.Deref(t1), _ ->
    let t1', g1, c1, phi1 = check_term env g c t1 in
    T.mk_term (T.Deref(t1')) (T.TPoly(a_l, r_l, lift_type ty)), g1, c1, phi1
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
  let t', _, _, _ = check_term StrMap.empty T.empty_gamma T.empty_capabilities t in
  t'
