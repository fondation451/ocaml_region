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

let rec convert_term t =
  T.mk_term
    (
      match S.get_term t with
      |S.Unit -> T.Unit
      |S.Bool(b) -> T.Bool(b)
      |S.Int(i) -> T.Int(i)
      |S.Var(v) -> T.Var(v)
      |S.Binop(op, t1, t2) -> T.Binop(op, convert_term t1, convert_term t2)
      |S.Not(t1) -> T.Not(convert_term t1)
      |S.Neg(t1) -> T.Neg(convert_term t1)
      |S.Comp(c, t1, t2) -> T.Comp(c, convert_term t1, convert_term t2)
      |S.Fun(f, arg_l, t1, t2) -> T.Fun(f, arg_l, convert_term t1, convert_term t2)
      |S.App(t1, t_l) -> T.App(convert_term t1, List.map convert_term t_l)
      |S.If(t1, t2, t3) -> T.If(convert_term t1, convert_term t2, convert_term t3)
      |S.Let(x, t1, t2) -> T.Let(x, convert_term t1, convert_term t2)
      |S.Letrec(x, t1, t2) -> T.Letrec(x, convert_term t1, convert_term t2)
      |S.Pair(t1, t2, t3) -> T.Pair(convert_term t1, convert_term t2, convert_term t3)
      |S.Fst(t1) -> T.Fst(convert_term t1)
      |S.Snd(t1) -> T.Snd(convert_term t1)
      |S.Hd(t1) -> T.Hd(convert_term t1)
      |S.Tl(t1) -> T.Tl(convert_term t1)
      |S.Nil(t1) -> T.Nil(convert_term t1)
      |S.Cons(t1, t2, t3) -> T.Cons(convert_term t1, convert_term t2, convert_term t3)
      |S.Ref(t1, t2) -> T.Ref(convert_term t1, convert_term t2)
      |S.Assign(t1, t2) -> T.Assign(convert_term t1, convert_term t2)
      |S.Deref(t1) -> T.Deref(convert_term t1)
      |S.Newrgn -> T.Newrgn
      |S.Aliasrgn(t1, t2) -> T.Aliasrgn(convert_term t1, convert_term t2)
      |S.Freergn(t1) -> T.Freergn(convert_term t1)
      |S.Sequence(t1, t2) -> T.Sequence(convert_term t1, convert_term t2)
    )
    (convert_ty (S.get_type t))
