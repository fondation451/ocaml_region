open Util

module S = Type
module T = Region

let region_of r = match r with |S.RRgn(rgn) |S.RAlpha(rgn) -> rgn

let rec convert_mty mty len =
  match mty with
  |S.TInt -> T.TInt
  |S.TBool -> T.TBool
  |S.TUnit -> T.TUnit
  |S.TAlpha(a) -> T.TAlpha(a)
  |S.TFun(mty_l, mty2, r) ->
    T.TFun(List.map (fun mty1 -> convert_mty mty1 len) mty_l, convert_mty mty2 len, region_of r)
  |S.TCouple(mty1, mty2, r) -> T.TCouple(convert_mty mty1 len, convert_mty mty2 len, region_of r)
  |S.TList(mty1, r) -> begin
    match len with
    |Some(i) -> T.TList(i, convert_mty mty1 len, region_of r)
    |None -> T.TList(-1, convert_mty mty1 len, region_of r)
  end

  |S.TRef(mty1, r) -> T.TRef(convert_mty mty1 len, region_of r)
  |S.THnd(r) -> T.THnd(region_of r)

let convert_ty (S.TPoly(alpha_l, rgn_l, mty)) len = T.TPoly(alpha_l, rgn_l, convert_mty mty len)

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

let list_length_mty mty =
  match mty with
  |T.TList(i, _, _) -> Some(i)
  |_ -> None

let rec list_length t env =
  match T.get_term t with
  |T.Unit |T.Bool(_) |T.Int(_) |T.Newrgn |T.Not(_) |T.Neg(_)
  |T.Binop(_, _, _) |T.Comp(_, _, _) |T.Pair(_, _, _)
  |T.Ref(_, _) |T.Assign(_, _) |T.Freergn(_)
  |T.Fun(_, _, _, _, _) ->
    None
  |T.Var(v) -> (try list_length_mty (StrMap.find v env) with Not_found -> None)
  |T.App(t1, t_l) ->
    let T.TPoly(_, _, T.TFun(_, mty2, _)) = T.get_type t1 in
    list_length_mty mty2
  |T.If(t1, t2, t3) -> begin
    match list_length t2 env, list_length t3 env with
    |None, None -> None
    |Some(out), None |None, Some(out) -> Some(out)
    |Some(out1), Some(out2) -> Some(max out1 out2)
  end
  |T.Match(t_match, t_nil, x, xs, t_cons) -> begin
    match list_length t_nil env, list_length t_cons env with
    |None, None -> None
    |Some(out), None |None, Some(out) -> Some(out)
    |Some(out1), Some(out2) -> Some(max out1 out2)
  end
  |T.Let(x, t1, t2) |T.Letrec(x, t1, t2) ->
    let T.TPoly(_, _, mty1) = T.get_type t1 in
    list_length t2 (StrMap.add x mty1 env)
    
  |T.Fst(t1) ->
    let T.TPoly(_, _, T.TCouple(mty1, _, _)) = T.get_type t1 in
    list_length_mty mty1
  |T.Snd(t1) ->
    let T.TPoly(_, _, T.TCouple(_, mty2, _)) = T.get_type t1 in
    list_length_mty mty2
  |T.Hd(t1) ->
    let T.TPoly(_, _, T.TList(_, mty1, _)) = T.get_type t1 in
    list_length_mty mty1
  |T.Tl(t1) ->
    let T.TPoly(_, _, T.TList(i, _, _)) = T.get_type t1 in
    Some(i-1)
  |T.Nil -> Some(0)
  |T.Cons(t1, t2, t3) ->
    let T.TPoly(_, _, T.TList(i, _, _)) = T.get_type t2 in
    Some(i+1)
  |T.Deref(t1) ->
    let T.TPoly(_, _, T.TRef(mty1, _)) = T.get_type t1 in
    list_length_mty mty1
  |T.Aliasrgn(t1, t2) -> list_length t2 env
  |T.Sequence(t1, t2) -> list_length t2 env

let rec convert_term t env =
  let te =
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
      match S.get_type t with
      |S.TPoly(_, _, S.TFun(arg_l_mty, _, _)) ->
        let env' =
          List.fold_left2
            (fun out x x_mty -> StrMap.add x (convert_mty x_mty None) out)
            env arg_l arg_l_mty
        in
        T.Fun
          (
            f,
            arg_l,
            convert_term t1 env',
            convert_term t2 env,
            convert_fun_pot
              f_pot
              env'
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
    |S.Nil -> T.Nil
    |S.Cons(t1, t2, t3) -> T.Cons(convert_term t1 env, convert_term t2 env, convert_term t3 env)
    |S.Ref(t1, t2) -> T.Ref(convert_term t1 env, convert_term t2 env)
    |S.Assign(t1, t2) -> T.Assign(convert_term t1 env, convert_term t2 env)
    |S.Deref(t1) -> T.Deref(convert_term t1 env)
    |S.Newrgn -> T.Newrgn
    |S.Aliasrgn(t1, t2) -> T.Aliasrgn(convert_term t1 env, convert_term t2 env)
    |S.Freergn(t1) -> T.Freergn(convert_term t1 env)
    |S.Sequence(t1, t2) -> T.Sequence(convert_term t1 env, convert_term t2 env)
    in
    let len = list_length (T.mk_term te (T.TPoly([], [], T.TUnit))) env in
    let ty = convert_ty (S.get_type t) len in
    T.mk_term te ty

let convert t = convert_term t StrMap.empty
