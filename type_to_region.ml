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
  |S.TFun(mty_l, mty2, r) -> T.TFun(List.map convert_mty mty_l, convert_mty mty2, region_of r)
  |S.TCouple(mty1, mty2, r) -> T.TCouple(convert_mty mty1, convert_mty mty2, region_of r)
  |S.TList(mty1, r) -> T.TList(convert_mty mty1, region_of r)
  |S.TRef(mty1, r) -> T.TRef(convert_mty mty1, region_of r)
  |S.THnd(r) -> T.THnd(region_of r)

let convert_ty (S.TPoly(alpha_l, rgn_l, mty)) = T.TPoly(alpha_l, rgn_l, convert_mty mty)

let region_of_mty mty =
  match mty with
  |T.THnd(r) -> r
  |_ -> assert false

let rec convert_p p arg_l =
  match p with
  |S.PPot(v) -> T.PPot(v)
  |S.PLit(i) -> T.PLit(i)
  |S.PSize(s) -> T.PSize(List.assoc s arg_l)
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

let rec convert_term t env =
  let ty = convert_ty (S.get_type t) in
  T.mk_term
    (
      match S.get_term t with
      |S.Unit -> T.Unit
      |S.Bool(b) -> T.Bool(b)
      |S.Int(i) -> T.Int(i)
      |S.Var(v) -> T.Var(v)
      |S.Binop(op, t1, t2) -> T.Binop(op, convert_term t1 env, convert_term t2 env)
      |S.Not(t1) -> T.Not(convert_term t1 env)
      |S.Neg(t1) -> T.Neg(convert_term t1 env)
      |S.Comp(cop, t1, t2) -> T.Comp(cop, convert_term t1 env, convert_term t2 env)
      |S.Fun(f, arg_l, t1, t2, f_pot) -> begin
        match ty with
        |T.TPoly(_, _, T.TFun(arg_l_ty, _, _)) ->
          T.Fun
            (
              f,
              arg_l,
              convert_term t1 env,
              convert_term t2 env,
              convert_fun_pot
                f_pot
                (List.fold_left2 (fun out x x_ty -> StrMap.add x x_ty out) env arg_l arg_l_ty)
                (List.mapi (fun i v -> v, i) arg_l)
            )
        |_ -> assert false
      end
      |S.App(t1, t_l) -> T.App(convert_term t1 env, List.map (fun t2 -> convert_term t2 env) t_l)
      |S.If(t1, t2, t3) -> T.If(convert_term t1 env, convert_term t2 env, convert_term t3 env)
      |S.Match(t_match, t_nil, x, xs, t_cons) ->
        T.Match(convert_term t_match env, convert_term t_nil env, x, xs, convert_term t_cons env)
      |S.Let(x, t1, t2) ->
        let t1' = convert_term t1 env in
        let T.TPoly(_, _, mty) = T.get_type t1' in
        T.Let(x, t1', convert_term t2 (StrMap.add x mty env))
      |S.Letrec(x, t1, t2) ->
        let t1' = convert_term t1 env in
        let T.TPoly(_, _, mty) = T.get_type t1' in
        T.Letrec(x, t1', convert_term t2 (StrMap.add x mty env))
      |S.Pair(t1, t2, t3) -> T.Pair(convert_term t1 env, convert_term t2 env, convert_term t3 env)
      |S.Fst(t1) -> T.Fst(convert_term t1 env)
      |S.Snd(t1) -> T.Snd(convert_term t1 env)
      |S.Hd(t1) -> T.Hd(convert_term t1 env)
      |S.Tl(t1) -> T.Tl(convert_term t1 env)
      |S.Nil(t1) -> T.Nil(convert_term t1 env)
      |S.Cons(t1, t2, t3) -> T.Cons(convert_term t1 env, convert_term t2 env, convert_term t3 env)
      |S.Ref(t1, t2) -> T.Ref(convert_term t1 env, convert_term t2 env)
      |S.Assign(t1, t2) -> T.Assign(convert_term t1 env, convert_term t2 env)
      |S.Deref(t1) -> T.Deref(convert_term t1 env)
      |S.Newrgn -> T.Newrgn
      |S.Aliasrgn(t1, t2) -> T.Aliasrgn(convert_term t1 env, convert_term t2 env)
      |S.Freergn(t1) -> T.Freergn(convert_term t1 env)
      |S.Sequence(t1, t2) -> T.Sequence(convert_term t1 env, convert_term t2 env)
    )
    ty

let convert t = convert_term t StrMap.empty
