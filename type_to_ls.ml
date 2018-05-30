(* open Util

module S = Type
module T = Ls

exception Error of string

let str_of_subs s =
  Printf.sprintf "%s\n" (strmap_str s T.show_list_sized)

let rec fv ls out=
  match ls with
  |T.LSize(_) -> out
  |T.LAlpha(vl) -> StrSet.add vl out
  |T.LPred(ls') |T.LSucc(ls') -> fv ls' out

let fv_mty mty =
  let rec loop mty out =
    match mty with
    |T.TAlpha(_) |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> out
    |T.TFun(mty_l, mty2, _) ->
      List.fold_left (fun out mty1 -> loop mty1 out) (loop mty2 out) mty_l
    |T.TCouple(mty1, mty2, _) -> loop mty1 (loop mty2 out)
    |T.TRef(mty1, _) -> loop mty1 out
    |T.TList(ls, mty1, _) -> loop mty1 (fv ls out)
  in loop mty StrSet.empty

(* StrSet.diff (fv_mty mty) (StrSet.of_list vl_l) *)

let fv_mty_l mty_l =

  List.fold_left (fun out mty -> StrSet.union (fv_mty mty) out) StrSet.empty mty_l

let rec apply s ls =
  match ls with
  |T.LSize(_) -> ls
  |T.LAlpha(vl) -> (try StrMap.find vl s with Not_found -> ls)
  |T.LPred(ls') -> T.LPred(apply s ls')
  |T.LSucc(ls') -> T.LSucc(apply s ls')

let rec apply_mty s mty =
  match mty with
  |T.TAlpha(_) |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> mty
  |T.TFun(mty_l, mty2, r) ->
    T.TFun(List.map (fun mty1 -> apply_mty s mty1) mty_l, apply_mty s mty2, r)
  |T.TCouple(mty1, mty2, r) -> T.TCouple(apply_mty s mty1, apply_mty s mty2, r)
  |T.TList(ls, mty1, r) -> T.TList(apply s ls, apply_mty s mty1, r)
  |T.TRef(mty1, r) -> T.TRef(apply_mty s mty1, r)

let remove_subs vl_l s = List.fold_left (fun out vl -> StrMap.remove vl out) s vl_l

let subs_empty = StrMap.empty

let remove_env env var = StrMap.remove var env

let fv_env env = fv_mty_l (List.rev_map snd (StrMap.bindings env))

let apply_env s env = StrMap.map (apply_mty s) env

let generalize env mty = StrSet.elements (fv_mty mty)

let instanciate mty =
  let vl_l = StrSet.elements (fv_mty mty) in
  let vl_l' = List.map (fun _ -> T.LAlpha(mk_var ())) vl_l in
  let s =
    List.fold_left2
      (fun out vl vl' -> StrMap.add vl vl' out)
      StrMap.empty vl_l vl_l'
  in
  apply_mty s mty

let rec varbind ls1 ls2 =
  match ls1, ls2 with
  |T.LSize(_), T.LSize(_) -> subs_empty
  |T.LAlpha(vl1), _ -> StrMap.singleton vl1 ls2
  |_, T.LAlpha(vl2) -> StrMap.singleton vl2 ls1
  |T.LAlpha(vl1), T.LAlpha(vl2) ->
    if vl1 = vl2 then subs_empty else StrMap.singleton vl1 ls2
  |T.LPred(ls1'), T.LPred(ls2') |T.LSucc(ls1'), T.LSucc(ls2') -> varbind ls1' ls2'

let rec mgu mty1 mty2 =
  match mty1, mty2 with
  |T.TFun(arg_l1, dst1, _), T.TFun(arg_l2, dst2, _) ->
    let s1 =
      List.fold_left2
        (fun out arg1 arg2 -> compose_subs (mgu arg1 arg2) out)
        subs_empty arg_l1 arg_l2
    in
    let s2 = mgu (apply_mty s1 dst1) (apply_mty s1 dst2) in
    compose_subs s1 s2
  |T.TCouple(mty1, mty2, _), T.TCouple(mty1', mty2', _) ->
    let s1 = mgu mty1 mty1' in
    let s2 = mgu (apply_mty s1 mty2) (apply_mty s1 mty2') in
    compose_subs s1 s2
  |T.TRef(mty1, _), T.TRef(mty1', _) -> mgu mty1 mty1'
  |T.TList(ls, mty1, _), T.TList(ls', mty1', _) ->
    let s1 = mgu mty1 mty1' in
    let s2 = varbind ls ls' in
    compose_subs s1 s2
  |_ -> subs_empty

and compose_subs s1 s2 =
  if s1 = subs_empty then s2
  else if s2 = subs_empty then s1
  else (
  Printf.printf "\nCALL compose_subs : %s\n%s\n\n" (str_of_subs s2) (str_of_subs s1);
  let acc_s = ref subs_empty in
  let s = StrMap.union
    (fun k ls1 ls2 ->
      let s = varbind ls1 ls2 in
      acc_s := compose_subs s !acc_s;
      let out = apply s ls1 in
      Some(out))
    (StrMap.map (apply s1) s2) s1
  in
  compose_subs !acc_s s
)

let remove_env env var = StrMap.remove var env

let rgn_of t =
  match T.get_type t with
  |T.THnd(r) -> r
  |_ -> assert false

let rec lift_mty mty =
  match mty with
  |S.TInt -> T.TInt |S.TBool -> T.TBool
  |S.TUnit -> T.TUnit |S.TAlpha(a) -> T.TAlpha(a)
  |S.TFun(mty_l, mty2, r) -> T.TFun(List.map lift_mty mty_l, lift_mty mty2, r)
  |S.TCouple(mty1, mty2, r) -> T.TCouple(lift_mty mty1, lift_mty mty2, r)
  |S.TList(mty1, r) -> T.TList(T.LAlpha(mk_var ()), lift_mty mty1, r)
  |S.TRef(mty1, r) -> T.TRef(lift_mty mty1, r)
  |S.THnd(r) -> T.THnd(r)

let rec find_var_mty t x =
  let rec loop t =
    let attempt t out =
      match out with
      |None -> loop t
      |_ -> out
    in
    match S.get_term t with
    |S.Unit |S.Bool(_) |S.Int(_) |S.Nil |S.Newrgn -> None
    |S.Var(x') -> if x = x' then (Some(S.get_type t)) else None
    |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1)
    |S.Hd(t1) |S.Tl(t1) |S.Deref(t1) |S.Freergn(t1) ->
      attempt t1 None
    |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2)
    |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) ->
      attempt t2 (attempt t1 None)
    |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) ->
      attempt t3 (attempt t2 (attempt t1 None))
    |S.App(t1, t_l) ->
      List.fold_left (fun out t2 -> attempt t2 out) (attempt t1 None) t_l
    |S.Fun(_, x_l, t1, t2, _) ->
      if List.mem x x_l then attempt t2 None else attempt t2 (attempt t1 None)
    |S.Let(x', t1, t2) |S.Letrec(x', t1, t2) ->
      if x = x' then attempt t2 None else attempt t2 (attempt t1 None)
    |S.Match(t1, t2, x', xs, t3) ->
      if x = x' || x = xs then
        attempt t2 (attempt t1 None)
      else
        attempt t3 (attempt t2 (attempt t1 None))
  in
  match loop t with
  |None -> raise (Error "find_var_mty")
  |Some(S.TPoly(_, _, out)) -> out

let rec process_ls env t =
  Printf.printf "--------- LS PROCCES ------------\n%s\n\n" (S.show_typed_term t);
  let te = S.get_term t in
  let (S.TPoly(alpha_l, rgn_l, mty)) = S.get_type t in
  let (s, te', mty') =
    match te with
    |S.Var(var) ->
      let mty' = instanciate (StrMap.find var env) in
      subs_empty, T.Var(var), mty'
      (* , (generalize env mty') *)
    |S.Unit -> subs_empty, T.Unit, T.TUnit
    |S.Bool(b) -> subs_empty, T.Bool(b), T.TBool
    |S.Int(i) -> subs_empty, T.Int(i), T.TInt
    |S.Binop(op, t1, t2) ->
      let (s1, t1') = process_ls env t1 in
      let (s2, t2') = process_ls (apply_env s1 env) t2 in
      let s = compose_subs s1 s2 in
      let mty' = apply_mty s (T.get_type t1') in
      s, T.Binop(op, t1', t2'), mty'
    |S.Not(t1) ->
      let (s1, t1') = process_ls env t1 in
      let mty' = apply_mty s1 (T.get_type t1') in
      s1, T.Not(t1'), mty'
    |S.Neg(t1) ->
      let (s1, t1') = process_ls env t1 in
      let mty' = apply_mty s1 (T.get_type t1') in
      s1, T.Neg(t1'), mty'
    |S.Comp(c, t1, t2) ->
      let (s1, t1') = process_ls env t1 in
      let (s2, t2') = process_ls (apply_env s1 env) t2 in
      let s = compose_subs s1 s2 in
      let mty' = apply_mty s (T.get_type t1') in
      s, T.Comp(c, t1', t2'), mty'
    |S.Fun(f, x_l, t1, t2, pot) ->
      let env' =
        List.fold_left
          (fun out x -> StrMap.add x (lift_mty (find_var_mty t1 x)) out)
          env (f::x_l)
      in
      let (s1, t1') = process_ls env' t1 in
      let (s2, t2') = process_ls (apply_env s1 env) t2 in
      let s = compose_subs s1 s2 in
      let mty1 = apply_mty s (T.get_type t1') in
      let r = rgn_of t2' in
      let mty' =
        T.TFun(List.map (fun x -> apply_mty s (StrMap.find x env')) x_l, mty1, r)
      in
      let s3 = mgu (apply_mty s (StrMap.find f env')) mty' in
      let s = compose_subs s s3 in
      s, T.Fun(f, x_l, t1', t2', pot), mty'
    |S.App(t1, t2_l) ->
      let (s1, t1') = process_ls env t1 in
      let (s2, t2_l') =
        List.fold_right
          (fun t2 (s, t2_l') ->
            let s2, t2' = process_ls (apply_env s env) t2 in
            compose_subs s2 s, t2'::t2_l')
          t2_l (subs_empty, [])
      in
      let s = compose_subs s1 s2 in
      let (T.TFun(mty_l, mty', _)) = apply_mty s (T.get_type t1') in
      let s =
        List.fold_left2
          (fun out mty1 t2' ->
            compose_subs out (mgu mty1 (apply_mty out (T.get_type t2'))))
          s mty_l t2_l'
      in
      let mty' = apply_mty s mty' in
      s, T.App(t1', t2_l'), mty'
    |S.If(t1, t2, t3) ->
      let s1, t1' = process_ls env t1 in
      let env = (apply_env s1 env) in
      let s2, t2' = process_ls env t2 in
      let env = (apply_env s2 env) in
      let s3, t3' = process_ls env t3 in
      let s = compose_subs s3 (compose_subs s2 s1) in
      let mty' = apply_mty s (T.get_type t3') in
      s, T.If(t1', t2', t3'), mty'
    |S.Match(t_match, t_nil, x, xs, t_cons) ->
      let s1, t_match' = process_ls env t_match in
      let env = (apply_env s1 env) in
      let s2, t_nil' = process_ls env t_nil in
      let s = compose_subs s1 s2 in
      let (T.TList(ls, mty_x, r)) = apply_mty s (T.get_type t_match') in
      let env =
        StrMap.add x mty_x (StrMap.add xs (T.TList(T.LPred(ls), mty_x, r)) env)
      in
      let s3, t_cons' = process_ls env t_cons in
      let s = compose_subs s3 s in
      let mty' = apply_mty s (T.get_type t_cons') in
      s, T.Match(t_match', t_nil', x, xs, t_cons'), mty'
    |S.Let(x, t1, t2) ->
      let s1, t1' = process_ls env t1 in
      let env = StrMap.add x (apply_mty s1 (T.get_type t1')) env in
      let s2, t2' = process_ls (apply_env s1 env) t2 in
      let s = compose_subs s2 s1 in
      let mty' = apply_mty s (T.get_type t2') in
      s, T.Let(x, t1', t2'), mty'
    |S.Letrec(f, t1, t2) ->
      let s1, t1' = process_ls env t1 in
      let env = StrMap.add f (apply_mty s1 (T.get_type t1')) env in
      let s2, t2' = process_ls (apply_env s1 env) t2 in
      let s = compose_subs s2 s1 in
      let mty' = apply_mty s (T.get_type t2') in
      s, T.Letrec(f, t1', t2'), mty'
    |S.Pair(t1, t2, t3) ->
      let s1, t1' = process_ls env t1 in
      let env = apply_env s1 env in
      let s2, t2' = process_ls env t2 in
      let env = apply_env s2 env in
      let s3, t3' = process_ls env t3 in
      let s = compose_subs s3 (compose_subs s2 s1) in
      let mty1 = apply_mty s (T.get_type t1') in
      let mty2 = apply_mty s (T.get_type t2') in
      let r = rgn_of t3' in
      let mty' = T.TCouple(mty1, mty2, r) in
      s, T.Pair(t1', t2', t3'), mty'
    |S.Fst(t1) ->
      let s1, t1' = process_ls env t1 in
      let (T.TCouple(mty', _, _)) = T.get_type t1' in
      s1, T.Fst(t1'), mty'
    |S.Snd(t1) ->
      let s1, t1' = process_ls env t1 in
      let (T.TCouple(_, mty', _)) = T.get_type t1' in
      s1, T.Snd(t1'), mty'
    |S.Hd(t1) ->
      let s1, t1' = process_ls env t1 in
      let (T.TList(_, mty', _)) = T.get_type t1' in
      s1, T.Hd(t1'), mty'
    |S.Tl(t1) ->
      let s1, t1' = process_ls env t1 in
      let (T.TList(ls, mty1, r)) = T.get_type t1' in
      let mty' = T.TList(T.LPred(ls), mty1, r) in
      s1, T.Tl(t1'), mty'
    |S.Nil ->
      let (S.TList(mty1, r)) = mty in
      let mty' = T.TList(T.LSize(0), lift_mty mty1, r) in
      subs_empty, T.Nil, mty'
    |S.Cons(t1, t2, t3) ->
      let s1, t1' = process_ls env t1 in
      let env = apply_env s1 env in
      let s2, t2' = process_ls env t2 in
      let env  = apply_env s2 env in
      let s3, t3' = process_ls env t3 in
      let s = compose_subs s3 (compose_subs s2 s1) in
      let mty1 = apply_mty s (T.get_type t1') in
      let (T.TList(ls, _, _)) = apply_mty s (T.get_type t2') in
      let r = rgn_of t3' in
      let mty' = T.TList(T.LSucc(ls), mty1, r) in
      s, T.Cons(t1', t2', t3'), mty'
    |S.Ref(t1, t2) ->
      let s1, t1' = process_ls env t1 in
      let env = apply_env s1 env in
      let s2, t2' = process_ls env t2 in
      let s = compose_subs s1 s2 in
      let mty1 = apply_mty s (T.get_type t1') in
      let r = rgn_of t2' in
      let mty' = T.TRef(mty1, r) in
      s, T.Ref(t1', t2'), mty'
    |S.Assign(t1, t2) ->
      let s1, t1' = process_ls env t1 in
      let env = apply_env s1 env in
      let s2, t2' = process_ls env t2 in
      let s = compose_subs s2 s1 in
      let mty' = T.TUnit in
      s, T.Assign(t1', t2'), mty'
    |S.Deref(t1) ->
      let s1, t1' = process_ls env t1 in
      let (T.TRef(mty', _)) = apply_mty s1 (T.get_type t1') in
      s1, T.Deref(t1'), mty'
    |S.Newrgn ->
      let (S.THnd(r)) = mty in
      let mty' = T.THnd(r) in
      subs_empty, T.Newrgn, mty'
    |S.Aliasrgn(t1, t2) ->
      let s1, t1' = process_ls env t1 in
      let env = apply_env s1 env in
      let s2, t2' = process_ls env t2 in
      let s = compose_subs s2 s1 in
      let mty' = apply_mty s (T.get_type t2') in
      s, T.Aliasrgn(t1', t2'), mty'
    |S.Freergn(t1) ->
      let s1, t1' = process_ls env t1 in
      let mty' = T.TUnit in
      s1, T.Freergn(t1'), mty'
    |S.Sequence(t1, t2) ->
      let s1, t1' = process_ls env t1 in
      let env = apply_env s1 env in
      let s2, t2' = process_ls env t2 in
      let s = compose_subs s2 s1 in
      let mty' = apply_mty s (T.get_type t2') in
      s, T.Sequence(t1', t2'), mty'
  in
  s, T.mk_term te' mty' alpha_l rgn_l

let process t =
  let s, t' = process_ls StrMap.empty t in
  Printf.printf "subs ls : %s\n\n" (str_of_subs s);
  t' *)

open Util

module S = Type
module T = Ls

let rgn_of t =
  match T.get_type t with
  |T.THnd(r) -> r
  |_ -> assert false
(*
let rec find_var_mty t x =
  let rec loop t =
    let attempt t out =
      match out with
      |None -> loop t
      |_ -> out
    in
    match S.get_term t with
    |S.Unit |S.Bool(_) |S.Int(_) |S.Nil |S.Newrgn -> None
    |S.Var(x') -> if x = x' then (Some(S.get_type t)) else None
    |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1)
    |S.Hd(t1) |S.Tl(t1) |S.Deref(t1) |S.Freergn(t1) ->
      attempt t1 None
    |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2)
    |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) ->
      attempt t2 (attempt t1 None)
    |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) ->
      attempt t3 (attempt t2 (attempt t1 None))
    |S.App(t1, t_l) ->
      List.fold_left (fun out t2 -> attempt t2 out) (attempt t1 None) t_l
    |S.Fun(_, x_l, t1, t2, _) ->
      if List.mem x x_l then attempt t2 None else attempt t2 (attempt t1 None)
    |S.Let(x', t1, t2) |S.Letrec(x', t1, t2) ->
      if x = x' then attempt t2 None else attempt t2 (attempt t1 None)
    |S.Match(t1, t2, x', xs, t3) ->
      if x = x' || x = xs then
        attempt t2 (attempt t1 None)
      else
        attempt t3 (attempt t2 (attempt t1 None))
  in
  match loop t with
  |None -> raise (Error "find_var_mty")
  |Some(S.TPoly(_, _, out)) -> out *)

(* let rec lift_mty mty =
  match mty with
  |S.TInt -> T.TInt |S.TBool -> T.TBool
  |S.TUnit -> T.TUnit |S.TAlpha(a) -> T.TAlpha(a)
  |S.TFun(mty_l, mty2, r) -> T.TFun(List.map lift_mty mty_l, lift_mty mty2, r)
  |S.TCouple(mty1, mty2, r) -> T.TCouple(lift_mty mty1, lift_mty mty2, r)
  |S.TList(mty1, r) -> T.TList(T.LAlpha(mk_var ()), lift_mty mty1, r)
  |S.TRef(mty1, r) -> T.TRef(lift_mty mty1, r)
  |S.THnd(r) -> T.THnd(r) *)

let rec lift_t t =
  let te = S.get_term t in
  let (S.TPoly(alpha_l, rgn_l, mty)) = S.get_type t in
  T.mk_term
  (
    match te with
    |S.Var(var) -> T.Var(var) |S.Unit -> T.Unit
    |S.Bool(b) -> T.Bool(b) |S.Int(i) -> T.Int(i)
    |S.Binop(op, t1, t2) -> T.Binop(op, lift_t t1, lift_t t2)
    |S.Not(t1) -> T.Not(lift_t t1)
    |S.Neg(t1) -> T.Neg(lift_t t1)
    |S.Comp(c, t1, t2) -> T.Comp(c, lift_t t1, lift_t t2)
    |S.Fun(f, x_l, t1, t2, pot) -> T.Fun(f, x_l, lift_t t1, lift_t t2, pot)
    |S.App(t1, t2_l) -> T.App(lift_t t1, List.map lift_t t2_l)
    |S.If(t1, t2, t3) -> T.If(lift_t t1, lift_t t2, lift_t t3)
    |S.Match(t_match, t_nil, x, xs, t_cons) ->
      T.Match(lift_t t_match, lift_t t_nil, x, xs, lift_t t_cons)
    |S.Let(x, t1, t2) -> T.Let(x, lift_t t1, lift_t t2)
    |S.Letrec(f, t1, t2) -> T.Letrec(f, lift_t t1, lift_t t2)
    |S.Pair(t1, t2, t3) -> T.Pair(lift_t t1, lift_t t2, lift_t t3)
    |S.Fst(t1) -> T.Fst(lift_t t1)
    |S.Snd(t1) -> T.Snd(lift_t t1)
    |S.Hd(t1) -> T.Hd(lift_t t1)
    |S.Tl(t1) -> T.Tl(lift_t t1)
    |S.Nil -> T.Nil
    |S.Cons(t1, t2, t3) -> T.Cons(lift_t t1, lift_t t2, lift_t t3)
    |S.Ref(t1, t2) -> T.Ref(lift_t t1, lift_t t2)
    |S.Assign(t1, t2) -> T.Assign(lift_t t1, lift_t t2)
    |S.Deref(t1) -> T.Deref(lift_t t1)
    |S.Newrgn -> T.Newrgn
    |S.Aliasrgn(t1, t2) -> T.Aliasrgn(lift_t t1, lift_t t2)
    |S.Freergn(t1) -> T.Freergn(lift_t t1)
    |S.Sequence(t1, t2) -> T.Sequence(lift_t t1, lift_t t2)
  )
    (* (lift_mty mty) *)
    mty
    alpha_l
    rgn_l

let grow_ls ls =
  match ls with
  |None -> None
  |Some(i) -> Some(i+1)

let shrink_ls ls =
  match ls with
  |None -> None
  |Some(i) -> Some(i-1)

let rec list_returned mty =
  match mty with
  |T.TFun(mty_l, mty2, _) ->
    (List.exists list_returned mty_l) || list_returned mty2
  |T.TCouple(mty1, mty2, _) -> (list_returned mty1) || (list_returned mty2)
  |T.TRef(mty1, _) -> list_returned mty1
  |T.TList(_, _, _) -> true
  |_ -> false

let rec merge_mty mty_out mty_ls =
  match mty_out, mty_ls with
  |T.TFun(mty_l, mty2, r), T.TFun(mty_l', mty2', _) ->
    T.TFun(List.map2 merge_mty mty_l mty_l', merge_mty mty2 mty2', r)
  |T.TCouple(mty1, mty2, r), T.TCouple(mty1', mty2', _) ->
    T.TCouple(merge_mty mty1 mty1', merge_mty mty2 mty2', r)
  |T.TList(_, mty1, r), T.TList(ls, mty1', _) ->
    T.TList(ls, merge_mty mty1 mty1', r)
  |T.TRef(mty1, r), T.TRef(mty1', _) ->
    T.TRef(merge_mty mty1 mty1', r)
  |_ -> mty_out

let rec process_ls env_f env t =
  Printf.printf "--------- LS PROCCES ------------\n%s\n\n" (T.show_typed_term t);
  let te = T.get_term t in
  let mty = T.get_type t in
  let alpha_l = T.get_alpha_l t in
  let rgn_l = T.get_rgn_l t in
  let (te', mty') =
    match te with
    |T.Var(var) -> T.Var(var), StrMap.find var env
    |T.Unit -> T.Unit, mty
    |T.Bool(b) -> T.Bool(b), mty
    |T.Int(i) -> T.Int(i), mty
    |T.Binop(op, t1, t2) ->
      let t1' = process_ls env_f env t1 in
      T.Binop(op, t1', process_ls env_f env t2), T.get_type t1'
    |T.Not(t1) ->
      let t1' = process_ls env_f env t1 in
      T.Not(t1'), T.get_type t1'
    |T.Neg(t1) ->
      let t1' = process_ls env_f env t1 in
      T.Neg(t1'), T.get_type t1'
    |T.Comp(c, t1, t2) ->
      let t1' = process_ls env_f env t1 in
      T.Comp(c, t1', process_ls env_f env t2), T.get_type t1'
    |T.Fun(f, x_l, t1, t2, pot) -> te, mty
      (* let env' =
        List.fold_left
          (fun out x -> StrMap.add x (lift_mty (find_var_mty t1 x)) out)
          env (f::x_l)
      in
      let t1' = process_ls env_f env' t1 in
      let t2' = process_ls env_f env t2 in
      let mty1 = T.get_type t1' in
      let r = rgn_of t2' in
      T.Fun(f, x_l, t1', t2', pot),
      T.TFun(List.map (fun x -> StrMap.find x env') x_l, mty1, r) *)
    |T.App(t1, t2_l) -> begin
      let t1' = process_ls env_f env t1 in
      let t2_l' =
        List.fold_right (fun t2 t2_l' -> (process_ls env_f env t2)::t2_l') t2_l []
      in
      if list_returned mty then
        let (arg_l, t_fun) =
          match T.get_term t1' with
          |T.Var(v) -> StrMap.find v env_f
          |T.Fun(f, arg_l, t_fun, _, _) -> (arg_l, t_fun)
        in
        let tmp =
          List.fold_right2
            (fun x t2 out ->
              T.mk_term
                (T.Let(x, t2, out))
                (T.get_type out)
                (T.get_alpha_l out)
                (T.get_rgn_l out))
            arg_l t2_l' t_fun
        in
        T.App(t1', t2_l'), merge_mty mty (T.get_type (process_ls env_f env tmp))
      else
        T.App(t1', t2_l'), mty
    end
    |T.If(t1, t2, t3) ->
      let t3' = process_ls env_f env t3 in
      T.If(process_ls env_f env t1, process_ls env_f env t2, t3'), T.get_type t3'
    |T.Match(t_match, t_nil, x, xs, t_cons) -> begin
      let t_match' = process_ls env_f env t_match in
      let (T.TList(ls, mty_x, r)) = T.get_type t_match' in
      match ls with
      |Some(i) when i = 0 ->
        let t_nil' = process_ls env_f env t_nil in
        T.Match(t_match', t_nil', x, xs, t_cons), T.get_type t_nil'
      |_ ->
        let env =
          StrMap.add x mty_x
            (StrMap.add xs (T.TList(shrink_ls ls, mty_x, r)) env)
        in
        let t_cons' = process_ls env_f env t_cons in
        T.Match(t_match', t_nil, x, xs, t_cons'), T.get_type t_cons'
    end
    |T.Let(x, t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let env = StrMap.add x (T.get_type t1') env in
      let t2' = process_ls env_f env t2 in
      T.Let(x, t1', t2'), T.get_type t2'
    |T.Letrec(f, t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let env = StrMap.add f (T.get_type t1') env in
      let (T.Fun(f, arg_l, t_fun, _, _)) = T.get_term t1' in
      let env_f = StrMap.add f (arg_l, t_fun) env_f in
      let t2' = process_ls env_f env t2 in
      T.Letrec(f, t1', t2'), T.get_type t2'
    |T.Pair(t1, t2, t3) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let t3' = process_ls env_f env t3 in
      let mty1 = T.get_type t1' in
      let mty2 = T.get_type t2' in
      let r = rgn_of t3' in
      T.Pair(t1', t2', t3'), T.TCouple(mty1, mty2, r)
    |T.Fst(t1) ->
      let t1' = process_ls env_f env t1 in
      let (T.TCouple(mty', _, _)) = T.get_type t1' in
      T.Fst(t1'), mty'
    |T.Snd(t1) ->
      let t1' = process_ls env_f env t1 in
      let (T.TCouple(_, mty', _)) = T.get_type t1' in
      T.Snd(t1'), mty'
    |T.Hd(t1) ->
      let t1' = process_ls env_f env t1 in
      let (T.TList(_, mty', _)) = T.get_type t1' in
      T.Hd(t1'), mty'
    |T.Tl(t1) ->
      let t1' = process_ls env_f env t1 in
      let (T.TList(ls, mty1, r)) = T.get_type t1' in
      T.Tl(t1'), T.TList(shrink_ls ls, mty1, r)
    |T.Nil ->
      let (T.TList(_, mty1, r)) = mty in
      T.Nil, T.TList(Some(0), mty1, r)
    |T.Cons(t1, t2, t3) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let t3' = process_ls env_f env t3 in
      let mty1 = T.get_type t1' in
      let (T.TList(ls, _, _)) = T.get_type t2' in
      let r = rgn_of t3' in
      T.Cons(t1', t2', t3'), T.TList(grow_ls ls, mty1, r)
    |T.Ref(t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let mty1 = T.get_type t1' in
      let r = rgn_of t2' in
      T.Ref(t1', t2'), T.TRef(mty1, r)
    |T.Assign(t1, t2) -> T.Assign(process_ls env_f env t1, process_ls env_f env t2), T.TUnit
    |T.Deref(t1) ->
      let t1' = process_ls env_f env t1 in
      let (T.TRef(mty', _)) = T.get_type t1' in
      T.Deref(t1'), mty'
    |T.Newrgn ->
    T.Newrgn, mty
    |T.Aliasrgn(t1, t2) ->
      let t2' = process_ls env_f env t2 in
      T.Aliasrgn(process_ls env_f env t1, t2'), T.get_type t2'
    |T.Freergn(t1) -> T.Freergn(process_ls env_f env t1), T.TUnit
    |T.Sequence(t1, t2) ->
      let t2' = process_ls env_f env t2 in
      T.Sequence(process_ls env_f env t1, t2'), T.get_type t2'
  in
  T.mk_term te' mty' alpha_l rgn_l

let process t =
  let t' = process_ls StrMap.empty StrMap.empty (lift_t t) in
  t'
