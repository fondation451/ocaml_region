open Util

module S = Ls

module T = Simpl

let simpl_r r = match r with |S.RRgn(rgn) |S.RAlpha(rgn) -> rgn

let rec simpl_ls ls = ls

let rec convert_mty mty =
  match mty with
  |S.TInt -> T.TInt
  |S.TBool -> T.TBool
  |S.TUnit -> T.TUnit
  |S.TAlpha(a) -> T.TAlpha(a)
  |S.TFun(mty_l, mty2, r) ->
    T.TFun(List.map convert_mty mty_l, convert_mty mty2, simpl_r r)
  |S.TCouple(mty1, mty2, r) ->
    T.TCouple(convert_mty mty1, convert_mty mty2, simpl_r r)
  |S.TList(ls, mty1, r) -> T.TList(simpl_ls ls, convert_mty mty1, simpl_r r)
  |S.TRef(id, mty1, r) -> T.TRef(id, convert_mty mty1, simpl_r r)
  |S.THnd(r) -> T.THnd(simpl_r r)

let region_of_mty mty =
  match mty with
  |T.THnd(r) -> r
  |_ -> assert false

let rec convert_p p arg_l =
  match p with
  |S.PPot(v) -> T.PPot(v)
  |S.PLit(i) -> T.PLit(i)
  |S.PSize(s) -> T.PSize(List.assoc s arg_l)
  |S.PLen(s) -> T.PLen(List.assoc s arg_l)
  |S.PAdd(p1, p2) -> T.PAdd(convert_p p1 arg_l, convert_p p2 arg_l)
  |S.PMin(p1) -> T.PMin(convert_p p1 arg_l)
  |S.PMul(p1, p2) -> T.PMul(convert_p p1 arg_l, convert_p p2 arg_l)

let convert_pot (rgn, (pc, pd)) env arg_l =
  region_of_mty (StrMap.find rgn env), (convert_p pc arg_l, convert_p pd arg_l)

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

let rec process_t env t =
  let te = S.get_term t in
  let mty' = convert_mty (S.get_type t) in
  let alpha_l = S.get_alpha_l t in
  let rgn_l = S.get_rgn_l t in
  T.mk_term
    (
      match te with
      |S.Unit -> T.Unit
      |S.Bool(b) -> T.Bool(b)
      |S.Int(i) -> T.Int(i)
      |S.Var(v) -> T.Var(v)
      |S.Binop(op, t1, t2) -> T.Binop(op, process_t env t1, process_t env t2)
      |S.Not(t1) -> T.Not(process_t env t1)
      |S.Neg(t1) -> T.Neg(process_t env t1)
      |S.Comp(cop, t1, t2) -> T.Comp(cop, process_t env t1, process_t env t2)
      |S.Fun(f, arg_l, t1, t2, f_pot) -> begin
        match mty' with
        |T.TFun(arg_l_ty, _, _) ->
          let env' =
            List.fold_left2
              (fun out x x_ty -> StrMap.add x x_ty out)
              env arg_l arg_l_ty
          in
          T.Fun
            (
              f,
              arg_l,
              process_t env' t1,
              process_t env t2,
              convert_fun_pot f_pot env' (List.mapi (fun i v -> v, i) arg_l)
            )
        |_ -> assert false
      end
      |S.App(t1, t_l) -> T.App(process_t env t1, List.map (process_t env) t_l)
      |S.If(t1, t2, t3) -> T.If(process_t env t1, process_t env t2, process_t env t3)
      |S.Match(t_match, t_nil, x, xs, t_cons) ->
        T.Match(process_t env t_match, process_t env t_nil, x, xs, process_t env t_cons)
      |S.Let(x, t1, t2) ->
        let t1' = process_t env t1 in
        let mty1 = T.get_type t1' in
        T.Let(x, t1', process_t (StrMap.add x mty1 env) t2)
      |S.Letrec(x, t1, t2) ->
        let t1' = process_t env t1 in
        let mty1 = T.get_type t1' in
        T.Letrec(x, t1', process_t (StrMap.add x mty1 env) t2)
      |S.Pair(t1, t2, t3) -> T.Pair(process_t env t1, process_t env t2, process_t env t3)
      |S.Fst(t1) -> T.Fst(process_t env t1)
      |S.Snd(t1) -> T.Snd(process_t env t1)
      |S.Hd(t1) -> T.Hd(process_t env t1)
      |S.Tl(t1) -> T.Tl(process_t env t1)
      |S.Nil -> T.Nil
      |S.Cons(t1, t2, t3) -> T.Cons(process_t env t1, process_t env t2, process_t env t3)
      |S.Ref(t1, t2) -> T.Ref(process_t env t1, process_t env t2)
      |S.Assign(t1, t2) -> T.Assign(process_t env t1, process_t env t2)
      |S.Deref(t1) -> T.Deref(process_t env t1)
      |S.Newrgn -> T.Newrgn
      |S.Aliasrgn(t1, t2) -> T.Aliasrgn(process_t env t1, process_t env t2)
      |S.Freergn(t1) -> T.Freergn(process_t env t1)
      |S.Sequence(t1, t2) -> T.Sequence(process_t env t1, process_t env t2)
    )
    mty'
    alpha_l
    rgn_l

let process t = process_t StrMap.empty t
