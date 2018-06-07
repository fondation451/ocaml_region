open Util

module S = Type
module T = Ls

let rgn_of t =
  match T.get_type t with
  |T.THnd(r) -> r
  |_ -> assert false

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
    |S.MatchList(t_match, t_nil, x, xs, t_cons) ->
      T.MatchList(lift_t t_match, lift_t t_nil, x, xs, lift_t t_cons)
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
  |T.TRef(_, mty1, _) -> list_returned mty1
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
  |T.TRef(_, mty1, r), T.TRef(id, mty1', _) ->
    T.TRef(id, merge_mty mty1 mty1', r)
  |_ -> mty_out

let ref_env = Hashtbl.create 10

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
      if list_returned (T.get_type t1') then
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
        Printf.printf "OKK CA VA \n";
        T.App(t1', t2_l'), merge_mty mty (T.get_type (process_ls env_f env tmp))
      else
      ( Printf.printf "NUL !!!\n";
        T.App(t1', t2_l'), mty)
    end
    |T.If(t1, t2, t3) ->
      let t3' = process_ls env_f env t3 in
      T.If(process_ls env_f env t1, process_ls env_f env t2, t3'), T.get_type t3'
    |T.MatchList(t_match, t_nil, x, xs, t_cons) -> begin
      let t_match' = process_ls env_f env t_match in
      let (T.TList(ls, mty_x, r)) = T.get_type t_match' in
      match ls with
      |Some(i) when i = 0 ->
        let t_nil' = process_ls env_f env t_nil in
        T.MatchList(t_match', t_nil', x, xs, t_cons), T.get_type t_nil'
      |_ ->
        let env =
          StrMap.add x mty_x
            (StrMap.add xs (T.TList(shrink_ls ls, mty_x, r)) env)
        in
        let t_cons' = process_ls env_f env t_cons in
        T.MatchList(t_match', t_nil, x, xs, t_cons'), T.get_type t_cons'
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
      let id = mk_id () in
      Hashtbl.replace ref_env id mty1;
      T.Ref(t1', t2'), T.TRef(id, mty1, r)
    |T.Assign(t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      let (T.TRef(id, _, _)) = T.get_type t1' in
      Hashtbl.replace ref_env id (T.get_type t2');
      Printf.printf "HASH TABLE REF\n";
      Hashtbl.iter (fun id mty -> Printf.printf "%d : %s\n" id (T.show_rcaml_type mty)) ref_env;
      T.Assign(t1', t2'), T.TUnit
    |T.Deref(t1) ->
      let t1' = process_ls env_f env t1 in
      let (T.TRef(id, _, _)) = T.get_type t1' in
      Printf.printf "HASH TABLE REF\n";
      Hashtbl.iter (fun id mty -> Printf.printf "%d : %s\n" id (T.show_rcaml_type mty)) ref_env;
      T.Deref(t1'), Hashtbl.find ref_env id
    |T.Newrgn -> T.Newrgn, mty
    |T.Aliasrgn(t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      T.Aliasrgn(t1', t2'), T.get_type t2'
    |T.Freergn(t1) -> T.Freergn(process_ls env_f env t1), T.TUnit
    |T.Sequence(t1, t2) ->
      let t1' = process_ls env_f env t1 in
      let t2' = process_ls env_f env t2 in
      T.Sequence(t1', t2'), T.get_type t2'
  in
  T.mk_term te' (merge_mty mty mty') alpha_l rgn_l

let process t =
  let t' = process_ls StrMap.empty StrMap.empty (lift_t t) in
  t'
