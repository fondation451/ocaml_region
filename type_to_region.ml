open Util

module S = Type
module T = Region




let region_of r = match r with |S.RRgn(rgn) |S.RAlpha(rgn) -> rgn

let rec convert_mty mty =
  match mty with
  |S.TInt -> T.TInt
  |S.TBool -> T.TBool
  |S.TUnit -> T.TUnit
  |S.TAlpha(a) -> T.TAlpha(a)
  |S.TFun(mty_l, mty2, r) ->
    T.TFun(List.map (fun mty1 -> convert_mty mty1) mty_l, convert_mty mty2, region_of r)
  |S.TCouple(mty1, mty2, r) -> T.TCouple(convert_mty mty1, convert_mty mty2, region_of r)
  |S.TList(mty1, r) -> T.TList(-1, convert_mty mty1, region_of r)

  |S.TRef(mty1, r) -> T.TRef(convert_mty mty1, region_of r)
  |S.THnd(r) -> T.THnd(region_of r)

let convert_ty (S.TPoly(alpha_l, rgn_l, mty)) = T.TPoly(alpha_l, rgn_l, convert_mty mty)

let rec merge_mty mty1 mty2 =
  match mty1, mty2 with
  |S.TInt, T.TInt |S.TBool, T.TBool |S.TUnit, T.TUnit -> mty2
  |S.THnd(r), T.THnd(_) -> T.THnd(region_of r)
  |S.TFun(arg_mty_l, mty2, r), T.TFun(arg_mty_l', mty2', _) ->
    T.TFun(List.map2 merge_mty arg_mty_l arg_mty_l', merge_mty mty2 mty2', region_of r)
  |S.TCouple(mty1, mty2, r), T.TCouple(mty1', mty2', _) ->
    T.TCouple(merge_mty mty1 mty1', merge_mty mty2 mty2', region_of r)
  |S.TList(mty1, r), T.TList(i, mty1', _) ->
    T.TList(i, merge_mty mty1 mty1', region_of r)
  |S.TRef(mty1, r), T.TRef(mty1', _) ->
    T.TRef(merge_mty mty1 mty1', region_of r)
  |S.TAlpha(a1), T.TAlpha(a2) when a1 = a2 -> T.TAlpha(a2)
  |_, T.TAlpha(a2) -> convert_mty mty1
  |S.TAlpha(a1), _ -> mty2
  |_ -> Printf.printf "Error %s %s" (S.show_rcaml_type mty1) (T.show_rcaml_type mty2); assert false


let region_of_mty mty =
  match mty with
  |T.THnd(r) -> r
  |_ -> assert false

let region_of_ty (T.TPoly(_, _, mty)) = region_of_mty mty

let mty_of (T.TPoly(_, _, mty)) = mty

let rec convert_p p arg_l =
  match p with
  |S.PPot(v) -> T.PPot(v)
  |S.PLit(i) -> T.PLit(i)
  |S.PSize(s) -> T.PSize(List.assoc s arg_l)
  |S.PLen(s) -> T.PLen(List.assoc s arg_l)
  |S.PAdd(p1, p2) -> T.PAdd(convert_p p1 arg_l, convert_p p2 arg_l)
  |S.PMin(p1) -> T.PMin(convert_p p1 arg_l)
  |S.PMul(p1, p2) -> T.PMul(convert_p p1 arg_l, convert_p p2 arg_l)

let convert_pot (rgn, (pc, pd)) env arg_l = region_of_mty (StrMap.find rgn env), (convert_p pc arg_l, convert_p pd arg_l)

let convert_pot_l pot_l env arg_l =
  let rec loop pot_l out =
    match pot_l with
    |[] -> out
    |(rgn, (pc, pd))::pot_l' -> begin
      try
        let (pc', pd') = List.assoc rgn out in
        loop pot_l' ((rgn, (T.PAdd(pc, pc'), T.PAdd(pd, pd')))::out)
      with Not_found -> loop pot_l' ((rgn, (pc, pd))::out)
    end
  in loop (List.map (fun pot -> convert_pot pot env arg_l) pot_l) []

let convert_fun_pot f_pot env arg_l =
  match f_pot with
  |None -> None
  |Some(pot_l) -> Some(convert_pot_l pot_l env arg_l)

let rec max_mty mty1 mty2 =
  match mty1, mty2 with
  |T.TFun(mty_l, mty2, r), T.TFun(mty_l', mty2', r') ->
    T.TFun(List.map2 (fun mty1 mty1' -> max_mty mty1 mty1') mty_l mty_l',
           max_mty mty2 mty2', r)
  |T.TCouple(mty1, mty2, r), T.TCouple(mty1', mty2', r') ->
    T.TCouple(max_mty mty1 mty1', max_mty mty2 mty2', r)
  |T.TList(i, mty1, r), T.TList(i', mty1', r') ->
    T.TList(max i i', max_mty mty1 mty1', r)
  |T.TRef(mty1, r), T.TRef(mty1', r') -> T.TRef(max_mty mty1 mty1', r)
  |_ -> mty1

let rec convert_term t env =
  let (S.TPoly(a_l, r_l, mty)) = S.get_type t in
  let te = S.get_term t in
  let ty_of mty' = T.TPoly(a_l, r_l, merge_mty mty mty') in
  match te with
  |S.Unit -> T.mk_term T.Unit (ty_of T.TUnit)
  |S.Bool(b) -> T.mk_term (T.Bool(b)) (ty_of T.TBool)
  |S.Int(i) -> T.mk_term (T.Int(i)) (ty_of T.TInt)
  |S.Var(v) ->
    T.mk_term
      (T.Var(v))
      (ty_of (try StrMap.find v env with Not_found -> convert_mty mty
        ))
  |S.Binop(op, t1, t2) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    T.mk_term (T.Binop(op, t1',  t2')) (T.get_type t1')
  |S.Not(t1) ->
    let t1' = convert_term t1 env in
    T.mk_term (T.Not(t1')) (T.get_type t1')
  |S.Neg(t1) ->
    let t1' = convert_term t1 env in
    T.mk_term (T.Neg(t1')) (T.get_type t1')
  |S.Comp(cop, t1, t2) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    T.mk_term (T.Comp(cop, t1', t2')) (T.get_type t1')
  |S.Fun(f, arg_l, t1, t2, f_pot) -> begin
    match mty with
    |S.TFun(arg_l_mty, _, _) ->
      let arg_l_mty' = List.map convert_mty arg_l_mty in
      let env' =
        List.fold_left2 (fun out x mty -> StrMap.add x
          mty out) env arg_l arg_l_mty'
      in
      let t1' = convert_term t1 env' in
      let t2' = convert_term t2 env in
      T.mk_term
        (T.Fun(f, arg_l, t1', t2',
               convert_fun_pot f_pot env' (List.mapi (fun i v -> v, i) arg_l)))
        (* (ty_of (T.TFun(arg_l_mty', mty_of (T.get_type t1'), region_of_ty (T.get_type t2')))) *)
        (ty_of (convert_mty mty))

    |_ -> assert false
  end
  |S.App(t1, t_l) ->
    let t1' = convert_term t1 env in
    let (T.TPoly(_, _, T.TFun(_, mty_out, _))) = T.get_type t1' in
    T.mk_term
      (T.App(t1', List.map (fun t2 -> convert_term t2 env) t_l))
      (ty_of mty_out)
  |S.If(t1, t2, t3) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    let t3' = convert_term t3 env in
    T.mk_term
      (T.If(t1', t2', t3'))
      (T.get_type t3')
  |S.Match(t_match, t_nil, x, xs, t_cons) ->
    let t_match' = convert_term t_match env in
    let t_nil' = convert_term t_nil env in
    let t_cons' = convert_term t_cons env in
    T.mk_term
      (T.Match(t_match', t_nil', x, xs, t_cons'))
      (T.get_type t_cons')
  |S.Let(x, t1, t2) ->
    let t1' = convert_term t1 env in
    let (T.TPoly(_, _, mty)) = T.get_type t1' in
    let t2' = convert_term t2 (StrMap.add x mty env) in
    T.mk_term
      (T.Let(x, t1', t2'))
      (T.get_type t2')
  |S.Letrec(x, t1, t2) ->
    let t1' = convert_term t1 env in
    let (T.TPoly(_, _, mty)) = T.get_type t1' in
    let t2' = convert_term t2 (StrMap.add x mty env) in
    T.mk_term
      (T.Letrec(x, t1', t2'))
      (T.get_type t2')
  |S.Pair(t1, t2, t3) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    let t3' = convert_term t3 env in
    T.mk_term
      (T.Pair(t1', t2', t3'))
      (ty_of (T.TCouple(mty_of (T.get_type t1'),
                        mty_of (T.get_type t2'),
                        region_of_ty (T.get_type t3'))))
  |S.Fst(t1) ->
    let t1' = convert_term t1 env in
    let (T.TPoly(_, _, T.TCouple(mty1, _, _))) = T.get_type t1' in
    T.mk_term (T.Fst(t1')) (ty_of mty1)
  |S.Snd(t1) ->
    let t1' = convert_term t1 env in
    let (T.TPoly(_, _, T.TCouple(_, mty2, _))) = T.get_type t1' in
    T.mk_term (T.Snd(t1')) (ty_of mty2)
  |S.Hd(t1) ->
    let t1' = convert_term t1 env in
    let (T.TPoly(_, _, T.TList(_, mty1, _))) = T.get_type t1' in
    T.mk_term (T.Hd(t1')) (ty_of mty1)
  |S.Tl(t1) ->
    let t1' = convert_term t1 env in
    let (T.TPoly(_, _, T.TList(i, mty1, r))) = T.get_type t1' in
    T.mk_term (T.Tl(t1')) (ty_of (T.TList(i-1, mty1, r)))
  |S.Nil ->
    let (S.TList(mty1, r)) = mty in
    T.mk_term T.Nil (ty_of (T.TList(0, convert_mty mty1, region_of r)))
  |S.Cons(t1, t2, t3) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    let t3' = convert_term t3 env in
    let (T.TPoly(_, _, mty1)) = T.get_type t1' in
    let (T.TPoly(_, _, T.TList(i, mty2, _))) = T.get_type t2' in
    let (T.TPoly(_, _, mty3)) = T.get_type t3' in
    T.mk_term
      (T.Cons(t1', t2', t3'))
      (ty_of (T.TList(i+1, max_mty mty1 mty2, region_of_mty mty3)))
  |S.Ref(t1, t2) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    T.mk_term
      (T.Ref(t1', t2'))
      (ty_of (T.TRef(mty_of (T.get_type t1'), region_of_ty (T.get_type t2'))))
  |S.Assign(t1, t2) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    T.mk_term (T.Assign(t1', t2')) (ty_of T.TUnit)
  |S.Deref(t1) ->
    let t1' = convert_term t1 env in
    let (T.TPoly(_, _, T.TRef(mty1, _))) = T.get_type t1' in
    T.mk_term (T.Deref(t1')) (ty_of mty1)
  |S.Newrgn ->
    let (S.THnd(r)) = mty in
    T.mk_term T.Newrgn (ty_of (T.THnd(region_of r)))
  |S.Aliasrgn(t1, t2) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    T.mk_term (T.Aliasrgn(t1', t2')) (T.get_type t2')
  |S.Freergn(t1) ->
    let t1' = convert_term t1 env in
    T.mk_term (T.Freergn(t1')) (ty_of T.TUnit)
  |S.Sequence(t1, t2) ->
    let t1' = convert_term t1 env in
    let t2' = convert_term t2 env in
    T.mk_term (T.Sequence(t1', t2')) (T.get_type t2')

let convert t = convert_term t StrMap.empty
