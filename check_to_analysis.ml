open Util

module S = Check
module H = Analysis

(**** Substitute rgn ****)

let rec merge_mty mty_src mty_dest out =
  match mty_src, mty_dest with
  |S.TFun(s, mty_src_l, mty_src', r1, _, _, _), S.TFun(s', mty_dest_l, mty_dest', r2, _, _, _) ->
    StrMap.add r1 r2
      (merge_mty mty_src' mty_dest'
        (List.fold_left2
          (fun out mty_src'' mty_dest'' -> merge_mty mty_src'' mty_dest'' out)
          (List.fold_left2
            (fun out (sr1, sr2) (sr1', sr2') -> StrMap.add sr1 sr1' (StrMap.add sr2 sr2' out)) out s s')
          mty_src_l mty_dest_l))
  |S.TCouple(mty_src', mty_src'', r1), S.TCouple(mty_dest', mty_dest'', r2) ->
    StrMap.add r1 r2 (merge_mty mty_src' mty_dest' (merge_mty mty_src'' mty_dest'' out))
  |S.TList(_, mty_src', r1), S.TList(_, mty_dest', r2) |S.TRef(_, mty_src', r1), S.TRef(_, mty_dest', r2) ->
    StrMap.add r1 r2 (merge_mty mty_src' mty_dest' out)
  |S.THnd(r1), S.THnd(r2) -> StrMap.add r1 r2 out
  |_ -> StrMap.empty

let apply_subs_r s r = try StrMap.find r s with Not_found -> r

let apply_subs_effect s phi =
  match phi with
  |S.ERead(r) -> S.ERead(apply_subs_r s r)
  |S.EWrite(r) -> S.EWrite(apply_subs_r s r)
  |S.EAlloc(r) -> S.EAlloc(apply_subs_r s r)

let rec apply_subs_mty s mty =
  match mty with
  |S.TFun(fs, mty_l, mty2, r, cin, cout, phi) ->
    S.TFun(List.map (fun (fsr1, fsr2) -> (apply_subs_r s fsr1, apply_subs_r s fsr2)) fs,
           List.map (apply_subs_mty s) mty_l, apply_subs_mty s mty2, apply_subs_r s r,
           List.map (fun (rc, cp) -> (apply_subs_r s rc, cp)) cin,
           List.map (fun (rc, cp) -> (apply_subs_r s rc, cp)) cout,
           List.map (apply_subs_effect s) phi)
  |S.TCouple(mty1, mty2, r) -> S.TCouple(apply_subs_mty s mty1, apply_subs_mty s mty2, apply_subs_r s r)
  |S.TList(ls, mty1, r) -> S.TList(ls, apply_subs_mty s mty1, apply_subs_r s r)
  |S.TRef(id, mty1, r) -> S.TRef(id, apply_subs_mty s mty1, apply_subs_r s r)
  |S.THnd(r) -> S.THnd(apply_subs_r s r)
  |_ -> mty

let rec apply_subs_pot s pot =
  match pot with
  |None -> None
  |Some(fun_pot_l) -> Some(List.map (fun (r, (p1, p2)) -> (apply_subs_r s r, (p1, p2))) fun_pot_l)

let rec apply_subs_t s sv t =
  let te = S.get_term t in
  let mty = S.get_type t in
  let alpha_l = S.get_alpha_l t in
  let rgn_l = S.get_rgn_l t in
  S.mk_term
    (match te with
     |S.Binop(op, t1, t2) -> S.Binop(op, apply_subs_t s sv t1, apply_subs_t s sv t2)
     |S.Not(t1) -> S.Not(apply_subs_t s sv t1)
     |S.Neg(t1) -> S.Neg(apply_subs_t s sv t1)
     |S.Comp(op, t1, t2) -> S.Comp(op, apply_subs_t s sv t1, apply_subs_t s sv t2)
     |S.Fun(name, arg_l, t1, t2, pot) -> S.Fun(name, arg_l, apply_subs_t s sv t1, apply_subs_t s sv t2, apply_subs_pot s pot)
     |S.App(t1, t_l) -> S.App(apply_subs_t s sv t1, List.map (apply_subs_t s sv) t_l)
     |S.If(t1, t2, t3) -> S.If(apply_subs_t s sv t1, apply_subs_t s sv t2, apply_subs_t s sv t3)
     |S.MatchList(t1, t2, x, xs, t3) -> S.MatchList(apply_subs_t s sv t1, apply_subs_t s sv t2, x, xs, apply_subs_t s sv t3)
     |S.Let(x, t1, t2) -> S.Let(x, apply_subs_t s (StrMap.remove x sv) t1, apply_subs_t s sv t2)
     |S.Letrec(x, t1, t2) -> S.Letrec(x, apply_subs_t s (StrMap.remove x sv) t1, apply_subs_t s sv t2)
     |S.Pair(t1, t2, t3) -> S.Pair(apply_subs_t s sv t1, apply_subs_t s sv t2, apply_subs_t s sv t3)
     |S.Fst(t1) -> S.Fst(apply_subs_t s sv t1)
     |S.Snd(t1) -> S.Snd(apply_subs_t s sv t1)
     |S.Hd(t1) -> S.Hd(apply_subs_t s sv t1)
     |S.Tl(t1) -> S.Tl(apply_subs_t s sv t1)
     |S.Cons(t1, t2, t3) -> S.Cons(apply_subs_t s sv t1, apply_subs_t s sv t2, apply_subs_t s sv t3)
     |S.Ref(t1, t2) -> S.Ref(apply_subs_t s sv t1, apply_subs_t s sv t2)
     |S.Assign(t1, t2) -> S.Assign(apply_subs_t s sv t1, apply_subs_t s sv t2)
     |S.Deref(t1) -> S.Deref(apply_subs_t s sv t1)
     |S.Aliasrgn(t1, t2) -> S.Aliasrgn(apply_subs_t s sv t1, apply_subs_t s sv t2)
     |S.Freergn(t1) -> S.Freergn(apply_subs_t s sv t1)
     |S.Sequence(t1, t2) -> S.Sequence(apply_subs_t s sv t1, apply_subs_t s sv t2)
     |_ -> te)
    (match te with
     |S.Var(x) -> (try StrMap.find x sv with Not_found -> apply_subs_mty s mty)
     |_ -> apply_subs_mty s mty)
    alpha_l
    rgn_l

let rec apply_subs s sv t_old t =
  if t <> t_old then
    apply_subs s sv t (apply_subs_t s sv t)
  else
    t

let subs s sv t =  apply_subs s sv t (apply_subs_t s sv t)

(********)

let fv_term t =
  let rec loop t out =
    match S.get_term t with
    |S.Unit |S.Bool(_) |S.Int(_) |S.Newrgn |S.Nil -> out
    |S.Var(v) ->StrSet.add v out
    |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1) |S.Hd(t1) |S.Tl(t1) |S.Deref(t1) |S.Freergn(t1) ->
      loop t1 out
    |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) |S.Fun(_, _, t1, t2, _)
    |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2) ->
      loop t1 (loop t2 out)
    |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) ->
      loop t1 (loop t2 (loop t3 out))
    |S.App(t1, t_l) -> List.fold_left (fun out t2 -> loop t2 out) (loop t1 out) t_l
    |S.MatchList(t1, t2, x, xs, t3) ->
      loop t1 (loop t2 (StrSet.remove x (StrSet.remove xs (loop t3 out))))
    |S.Let(x, t1, t2) |S.Letrec(x, t1, t2) ->
      loop t1 (StrSet.remove x (loop t2 out))
  in
  let tmp = (loop t StrSet.empty) in
  (* Printf.printf "MARDI DEBUG : %s\n\n" (strset_str tmp); *)
  tmp

let rec concrete_rgn t =
  match S.get_term t with
  |S.Newrgn -> begin
    match S.get_type t with
    |S.THnd(r) -> StrSet.singleton r
    |_ -> assert false
  end
  |S.Unit |S.Bool(_) |S.Int(_) |S.Var(_) |S.Newrgn |S.Nil -> StrSet.empty
  |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1) |S.Hd(t1) |S.Tl(t1) |S.Deref(t1) |S.Freergn(t1) ->
    concrete_rgn t1
  |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) |S.Fun(_, _, t1, t2, _) |S.Let(_, t1, t2)
  |S.Letrec(_, t1, t2) |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2) ->
    StrSet.union (concrete_rgn t1) (concrete_rgn t2)
  |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) |S.MatchList(t1, t2, _, _, t3) ->
    StrSet.union (concrete_rgn t1) (StrSet.union (concrete_rgn t2) (concrete_rgn t3))
  |S.App(t1, t_l) ->
    List.fold_left (fun out t2 -> StrSet.union (concrete_rgn t2) out) (concrete_rgn t1) t_l

let rec rgn_mty mty =
  match mty with
  |S.TInt |S.TBool |S.TUnit |S.TAlpha(_) -> StrSet.empty
  |S.TList(_, mty1, r) |S.TRef(_, mty1, r) -> StrSet.add r (rgn_mty mty1)
  |S.TCouple(mty1, mty2, r) -> StrSet.add r (StrSet.union (rgn_mty mty1) (rgn_mty mty2))
  |S.TFun(_, mty_l, mty2, r, _, _, _) ->
    List.fold_left (fun out mty1 -> StrSet.union (rgn_mty mty1) out) (StrSet.add r (rgn_mty mty2)) mty_l
  |S.THnd(r) -> StrSet.singleton r

let rec rgn_of t =
  StrSet.union
    (
      match S.get_term t with
      |S.Unit |S.Bool(_) |S.Int(_) |S.Var(_) |S.Newrgn |S.Nil -> StrSet.empty
      |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1) |S.Hd(t1) |S.Tl(t1) |S.Deref(t1) |S.Freergn(t1) ->
        rgn_of t1
      |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) |S.Fun(_, _, t1, t2, _) |S.Let(_, t1, t2)
      |S.Letrec(_, t1, t2) |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2) ->
        StrSet.union (rgn_of t1) (rgn_of t2)
      |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) |S.MatchList(t1, t2, _, _, t3) ->
        StrSet.union (rgn_of t1) (StrSet.union (rgn_of t2) (rgn_of t3))
      |S.App(t1, t_l) ->
        List.fold_left (fun out t2 -> StrSet.union (rgn_of t2) out) (rgn_of t1) t_l
    )
    (rgn_mty (S.get_type t))

let on_rgn r mty =
  match mty with
  |S.TInt |S.TBool |S.TUnit |S.TAlpha(_) -> false
  |S.TFun(_, _, _, r', _, _, _) |S.TCouple(_, _, r') |S.TList(_, _, r')
  |S.TRef(_, _, r') |S.THnd(r') -> r = r'

(*let fun_name t =
  match S.get_term t with
  |S.Var(v) -> v
  |S.Fun(f, _, _, _, _) -> f
  |_ -> assert false
*)

let from_coef c =
  match c with
  |Num.Int(out) -> out
  |_ -> assert false

let convert_coef c = Num.Int(c)

let convert_line pot =
  let rec loop pot coef const out =
    match pot with
    |H.PPot(v) -> const, (v, convert_coef coef)::out
    |H.PLit(i) -> i * coef + const, out
    |H.PAdd(p1, p2) ->
      let const1, out1 = loop p1 coef const out in
      loop p2 coef const1 out1
    |H.PMin(p1) -> loop p1 (-1 * coef) const out
    |H.PMul(_) -> assert false
    |H.PSize(_) -> assert false
    |H.PLen(_) -> assert false
  in
  let bound, out = loop pot 1 0 [] in
  -1 * bound, out

let convert_to_simplex m vars lin_prog =
  Printf.printf "%s :\n%s\n\n" m (H.show_integer_prog lin_prog);
  let sim = Simplex.create () in
  let rec loop_var sim vars =
    match vars with
    |[] -> sim
    |v::vars' -> loop_var (Simplex.add_var sim v) vars'
  in
  let rec loop_line sim lin_prog =
    match lin_prog with
    |[] -> sim
    |pot::lin_prog' ->
      let bound, line = convert_line pot in
      loop_line (Simplex.add_line sim line (Simplex.mk_const bound)) lin_prog'
  in
  loop_line (loop_var sim vars) lin_prog

let find_rgn_sub r s =
  let out = List.map fst (List.filter (fun (r1, r2) -> r2 = r) s) in
  match out with
  |[] ->
    if List.exists (fun (r1, r2) -> r1 = r) s then
      raise Not_found
    else
      [r]
  |_ -> out

let no_side_effect ty =
  match ty with
  |S.TFun(_, _, _, _, _, _, phi) ->
    List.for_all
      (fun e ->
        match e with
        |S.ERead(_) |S.EAlloc(_) -> true
        |S.EWrite(_) -> false)
      phi
  |_ -> assert false

let vars_of_exp (pot, _) = StrSet.singleton pot

let rec vars_of_pot out p =
  match p with
  |H.PPot(v) -> StrSet.add v out
  |H.PLit(_) |H.PSize(_) -> out
  |H.PMul(p1, p2) |H.PAdd(p1, p2) -> vars_of_pot (vars_of_pot out p1) p2
  |H.PMin(p1) -> vars_of_pot out p1

let vars_of_lines lines = List.fold_left vars_of_pot StrSet.empty lines

let get_rgn mty =
  match mty with
  |S.TInt |S.TBool |S.TUnit |S.TAlpha(_) -> assert false
  |S.TFun(_, _, _, r, _, _, _) |S.TCouple(_, _, r)
  |S.TList(_, _, r) |S.TRef(_, _, r) |S.THnd(r) -> r

let get_len mty =
  match mty with
  |S.TList(i, _, _) -> i
  |_ -> assert false

let rec instanciate_size i t_l out =
  match t_l with
  |[] -> (*H.PUnit, out*) assert false
  |hd::tl when i = 0 -> let r = get_rgn (S.get_type hd) in H.PPot(r), r::out
  |hd::tl -> instanciate_size (i-1) tl out

let rec instanciate_length i t_l out =
  match t_l with
  |[] -> assert false
  |hd::tl when i = 0 -> begin
    match get_len (S.get_type hd) with
    |Some(i) -> H.PLit(i), out
    |None -> let r = get_rgn (S.get_type hd) in H.PPot(r), r::out
  end
  |hd::tl -> instanciate_length (i-1) tl out

let rec simplify_lit p =
  let rec loop p =
    match p with
    |H.PAdd(p1, p2) -> begin
      let p1' = loop p1 in
      let p2' = loop p2 in
      match p1', p2' with
      |H.PLit(i), H.PLit(i') -> H.PLit(i + i')
      |H.PAdd(H.PLit(i'), p'), H.PLit(i)
      |H.PAdd(p', H.PLit(i')), H.PLit(i)
      |H.PLit(i), H.PAdd(H.PLit(i'), p')
      |H.PLit(i), H.PAdd(p', H.PLit(i')) -> H.PAdd(p', H.PLit(i + i'))
      |_ -> H.PAdd(p1', p2')
    end
    |H.PMul(p1, p2) -> begin
      let p1' = loop p1 in
      let p2' = loop p2 in
      match p1', p2' with
      |H.PLit(i), H.PLit(i') -> H.PLit(i * i')
      |H.PMul(H.PLit(i'), p'), H.PLit(i)
      |H.PMul(p', H.PLit(i')), H.PLit(i)
      |H.PLit(i), H.PMul(H.PLit(i'), p')
      |H.PLit(i), H.PMul(p', H.PLit(i')) -> H.PMul(p', H.PLit(i * i'))
      |_ -> H.PMul(p1', p2')
    end
    |H.PMin(p1) -> begin
      let p1' = loop p1 in
      match p1' with
      |H.PLit(i) -> H.PLit(-1 * i)
      |_ -> H.PMin(p1')
    end
    |_ -> p
  in loop p

let rec instanciate p t_l =
  let rec loop p t_l out =
    match p with
    |H.PPot(_) |H.PLit(_) -> p, out
    |H.PSize(i) -> instanciate_size i t_l out
    |H.PLen(i) -> instanciate_length i t_l out
    |H.PAdd(p1, p2) ->
      let p1', out = loop p1 t_l out in
      let p2', out = loop p2 t_l out in
      H.PAdd(p1', p2'), out
    |H.PMin(p1) ->
      let p1', out = loop p1 t_l out in
      H.PMin(p1'), out
    |H.PMul(p1, p2) ->
      let p1', out = loop p1 t_l out in
      let p2', out = loop p2 t_l out in
      H.PMul(p1', p2'), out
    |H.PUnit -> H.PUnit, out
  in
  let p', out = loop p t_l [] in
  simplify_lit p', out

let rec fresh_names_p p vars s =
  match p with
  |H.PPot(id) -> begin
    try
      H.PPot(StrMap.find id s), s
    with Not_found ->
      let new_id = H.mk_pot vars in
      H.PPot(new_id), StrMap.add id new_id s
  end
  |H.PLit(i) -> H.PLit(i), s
  |H.PSize(i) -> H.PSize(i), s
  |H.PAdd(p1, p2) ->
    let p1', s = fresh_names_p p1 vars s in
    let p2', s = fresh_names_p p2 vars s in
    H.PAdd(p1', p2'), s
  |H.PMin(p1) ->
    let p1', s = fresh_names_p  p1 vars s in
    H.PMin(p1'), s
  |H.PMul(p1, p2) ->
    let p1', s = fresh_names_p p1 vars s in
    let p2', s = fresh_names_p p2 vars s in
    H.PMul(p1', p2'), s
  |H.PUnit -> H.PUnit, s

let rec fresh_names p_l vars s =
  let rec loop p_l s out =
    match p_l with
    |[] -> out, s
    |h::t ->
      let h', s = fresh_names_p h vars s in
      loop t s (h'::out)
  in loop p_l s []

let link_lines r lines lin_progs =
  let rec link_line lines out =
    match lines with
    |H.PPot(v) when v <> r -> begin
      try
        let v_lines = List.assoc v lin_progs in
        List.rev_append v_lines out
      with Not_found -> out
    end
    |H.PAdd(p1, p2) -> link_line p2 (link_line p1 out)
    |H.PMin(p1) -> link_line p1 out
    |H.PMul(p1, p2) -> link_line p2 (link_line p1 out)
    |_ -> out
  in
  List.fold_left (fun out line -> link_line line out) lines lines

let env = Hashtbl.create 10
let add_fun_pot r f v = Hashtbl.add env (r, f) v
let mem_fun_pot r f = Hashtbl.mem env (r, f)
let find_fun_pot r f = Hashtbl.find env (r, f)
let remove_fun_pot r f = Hashtbl.remove env (r, f)

let print_fun_pot () =
  Hashtbl.iter
    (fun (r, f) (pc, pd, lines) ->
      Printf.printf
        "%s::%s : (%s, %s)\n%s\n\n"
        f r (H.show_pot pc) (H.show_pot pd)
        (List.fold_left (fun out p -> out ^ ";\n" ^ (H.show_pot p)) "" lines))
    env

let process_r r_l cr_l t =
  let vars = ref (StrSet.empty) in
  let saved_state = ref [] in
  let rec process_t t r_cost env_f =
(*  Printf.printf "--------- NO SIDE PROCCES ------------\n%s\n\n" (S.show_typed_term t);
  Printf.printf "ENV\n";
  Hashtbl.iter (fun (r, f) (c, d, lines) -> Printf.printf "%s %s : (%s, %s, %s)\n" f r c d (H.show_integer_prog lines)) env;
  Printf.printf "OUT\n";
  StrMap.iter (fun r (lines, n) -> Printf.printf "%s : %s\n%s\n" r n (H.show_integer_prog lines)) out;
  Printf.printf "\n\n";*)
(*   Printf.printf "--------- ANALISYS PROCESS ------------\n%s\n\n" (S.show_typed_term t); *)
    let te = S.get_term t in
    let mty = S.get_type t in
    match te with
    |S.Unit |S.Bool(_) |S.Int(_) |S.Nil |S.Var(_) ->
      StrMap.map
        (fun (lines, n) ->
          let m = H.PPot(H.mk_pot vars) in
          let new_line = H.PAdd(m, H.PMin  n) in
          new_line::lines, m)
        r_cost
    |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) -> process_t t2 (process_t t1 r_cost env_f) env_f
    |S.Not(t1) |S.Neg(t1) -> process_t t1 r_cost env_f
    |S.Fun(f, arg_l, t1, t2, pot) (*when no_side_effect mty*) -> (*begin
      let r_cost =*)
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r mty then
            let m = H.PPot(H.mk_pot' "fun" vars) in
            let fv_var = fv_term t1 in
            let nb_fv =
              StrSet.cardinal
                (StrSet.remove f
                  (List.fold_left
                    (fun out arg -> StrSet.remove arg out)
                    fv_var arg_l))
            in
            let new_line = H.PAdd(H.PAdd(m, H.PMin n), H.PLit(nb_fv * (cost_of RCLO))) in
            new_line::lines, m
          else
            lines, n)
        r_cost
(*      in
      match pot with
      |Some(fun_pot_l) ->
        List.iter (fun (r, (pc, pd)) -> add_fun_pot r f (pc, pd, [])) fun_pot_l;
        r_cost
      |None ->
        let l_n = List.map (fun (r, (lines, n)) -> r, n) (StrMap.bindings r_cost) in
        let l_c = List.map (fun (r, n) -> r, H.PPot(H.mk_pot' "c" vars)) l_n in
        let l_d = List.map (fun (r, n) -> r, H.PPot(H.mk_pot' "d" vars)) l_n in
        List.iter2 (fun (r, c) (r, d) -> add_fun_pot r f (c, d, [])) l_c l_d;
        let r_cost_f =
          StrMap.mapi
            (fun r (lines, d') ->
              let c = List.assoc r l_c in
              let d = List.assoc r l_d in
              if c <> d' then
                let new_line_fun = H.PAdd(d, H.PMin d') in
                new_line_fun::lines, d
              else
                [], c)
            (process_t t1 (StrMap.mapi (fun r (lines, n) -> [], List.assoc r l_c) r_cost) env_f)
        in
        StrMap.iter
          (fun r (lines, d) ->
            if lines <> [] then
              add_fun_pot r f (List.assoc r l_c, d, lines)
            else
              remove_fun_pot r f)
          r_cost_f;
        r_cost
    end*)
    |S.App((*s, *)t1, t_l) -> begin
      let r_cost = process_t t1 r_cost env_f in
      let (arg_l, fun_mty_l, t_fun, pot) =
        match S.get_term t1, S.get_type t1 with
        |S.Var(v), _ -> StrMap.find v env_f
        |S.Fun(f, arg_l, t_fun, _, pot), S.TFun(_, fun_mty_l, _, _, _, _, _) -> (arg_l, fun_mty_l, t_fun, pot)
      in
      match pot with
      |Some(fun_pot_l) ->
        let (S.TFun(s, _, _, _, _, _, _)) = S.get_type t1 in
        let l_n' = List.map (fun (r, (_, n')) -> r, n') (StrMap.bindings r_cost) in
        let r_cost = List.fold_left (fun r_cost t2 -> process_t t2 r_cost env_f) r_cost t_l in
        StrMap.mapi
          (fun r (lines, n'') ->
            let new_lines, n'' =
              let n' = List.assoc r l_n' in
              try
(*                Printf.printf "Dealing with %s\n" r;*)
                let r_sub_l = List.filter (fun r_sub -> List.mem_assoc r_sub fun_pot_l) (find_rgn_sub r s) in
(*               Printf.printf "APPICATION SUB REGION %s -> %s\n" r ("[" ^ (List.fold_left (fun out r -> Printf.sprintf "%s, %s" out r) "" r_sub_l) ^ "]");*)
                let out1, n', n'' = List.fold_left
                  (fun (out1, n', n'') r_sub ->
                    let cr, dr = List.assoc r_sub fun_pot_l in
     (*               let cr, dr, fun_lines = find_fun_pot r_sub (fun_name t1) in*)
                    let cr, r_cr = instanciate cr t_l in
                    let dr, r_dr = instanciate dr t_l in
                    let fun_lines, sub =
                      fresh_names
                        (List.fold_left
                          (fun fun_lines r ->
                            let rlines, _ = StrMap.find r r_cost in
                            List.rev_append rlines fun_lines)
                          [] (List.rev_append r_cr r_dr))
                        vars StrMap.empty
                    in
                    let cr, sub = fresh_names_p cr vars sub in
                    let dr, sub = fresh_names_p dr vars sub in
                  (* Printf.printf "APPLICATION OF %s with coef %s, %s\n" (fun_name t1) (H.show_pot cr) (H.show_pot dr); *)
                    (List.rev_append ((H.PAdd(H.PAdd(H.PAdd(n'', cr), H.PMin n'), H.PMin dr))::fun_lines) out1,
                    n'',
                    H.PPot(H.mk_pot vars)))
                  ([], n', n'')
                  r_sub_l
                in
                out1, n'
              with Not_found ->
(*                Printf.printf "App, Some not found !!!\n";*)
                if n'' <> n' then [H.PAdd(n'', H.PMin n')], n'' else [], n''
            in
            List.rev_append new_lines lines, n'')
          r_cost
(*
        List.fold_left
          (fun (r, (cr, dr)) ->
            let cr, r_cr = instanciate cr t_l in
            let dr, r_dr = instanciate dr t_l in
            let r_fun_lines =
              List.fold_left
                (fun out r ->
                  let l, _ = StrMap.find r r_cost in
                  List.rev_append l out)
                [] (List.rev_append r_dr r_cr)
            in
            (cr, dr, r_fun_lines))
          [] fun_pot_l*)
      |None ->
        let mty_l = List.map S.get_type t_l in
        let s = List.fold_left2 (fun out fun_mty mty -> merge_mty fun_mty mty out) StrMap.empty fun_mty_l mty_l in
        let sv = List.fold_left2 (fun out x tx -> StrMap.add x (S.get_type tx) out) StrMap.empty arg_l t_l in
        let t_fun' =
          List.fold_right2
            (fun x t2 out ->
              S.mk_term (S.Let(x, t2, out)) (S.get_type out) (S.get_alpha_l out) (S.get_rgn_l out))
              arg_l t_l (subs s sv t_fun)
        in
(*        Printf.printf "s : %s\n" (strmap_str s (fun x -> x));
        Printf.printf "t_fun : %s\n" (S.show_typed_term t_fun');*)
        process_t t_fun' r_cost env_f
    end
    |S.If(t1, t2, t3) ->
      let r_cost1 = process_t t1 r_cost env_f in
      let l_n1 = List.map (fun (r, (lines, n)) -> r, n) (StrMap.bindings r_cost1) in
      let r_cost2 = process_t t2 r_cost1 env_f in
      let l_n2 = List.map (fun (r, (lines, n)) -> r, n) (StrMap.bindings r_cost2) in
      let r_cost2' = StrMap.mapi (fun r (lines, _) -> lines, List.assoc r l_n1) r_cost2 in
      let r_cost3 = process_t t3 r_cost2' env_f in
      StrMap.mapi
        (fun r (lines, m3) ->
          let m2 = List.assoc r l_n2 in
          let m = H.PPot(H.mk_pot' "if" vars) in
          let new_line1 = H.PAdd(m, H.PMin m2) in
          let new_line2 = H.PAdd(m, H.PMin m3) in
          new_line1::new_line2::lines, m)
        r_cost3
    |S.MatchList(t_match, t_nil, x, xs, t_cons) -> assert false
    |S.Let(x, t1, t2) -> process_t t2 (process_t t1 r_cost env_f) env_f
    |S.Letrec(x, t1, t2) ->
      let (S.Fun(f, arg_l, t_fun, _, pot)) = S.get_term t1 in
      let (S.TFun(_, fun_mty_l, _, _, _, _, _)) = S.get_type t1 in
      let env_f = StrMap.add f (arg_l, fun_mty_l, t_fun, pot) env_f in
      process_t t2 r_cost env_f
    |S.Pair(t1, t2, t3) ->
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r mty then
            let m = H.PPot(H.mk_pot' "pair" vars) in
            let new_line = H.PAdd(H.PAdd(m, H.PMin n), H.PLit(cost_of RPAIR)) in
            new_line::lines, m
          else
            lines, n)
        (process_t t2 (process_t t1 r_cost env_f) env_f)
    |S.Fst(t1) |S.Snd(t1) |S.Hd(t1) |S.Tl(t1) -> process_t t1 r_cost env_f
    |S.Cons(t1, t2, t3) ->
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r mty then
            let m = H.PPot(H.mk_pot' "cons" vars) in
            let new_line = H.PAdd(H.PAdd(m, H.PMin n), H.PLit(cost_of RCONS)) in
            new_line::lines, m
          else
            lines, n)
        (process_t t2 (process_t t1 r_cost env_f) env_f)
    |S.Ref(t1, t2) -> process_t t2 (process_t t1 r_cost env_f) env_f
    |S.Assign(t1, t2) -> process_t t2 (process_t t1 r_cost env_f) env_f
    |S.Deref(t1) -> process_t t1 r_cost env_f
    |S.Newrgn ->
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r mty then
            let m = H.PPot(H.mk_pot' "hnd" vars) in
            let new_line = H.PAdd(H.PAdd(m, H.PMin n), H.PLit(cost_of RHND)) in
            new_line::lines, m
          else
            lines, n)
        r_cost
    |S.Aliasrgn(t1, t2) -> process_t t2 (process_t t1 r_cost env_f) env_f
    |S.Freergn(t1) ->
      let r_cost = process_t t1 r_cost env_f in
      let r = get_rgn (S.get_type t1) in
      saved_state := r_cost::(!saved_state);
      StrMap.remove r r_cost
    |S.Sequence(t1, t2) -> process_t t2 (process_t t1 r_cost env_f) env_f
  in
  let compute_lin_prog lin_prog memories =
    let lin_prog = List.map (fun (r, (lines, _)) -> r, lines) (StrMap.bindings lin_prog) in
    let lin_prog = List.filter (fun (r, lines) -> List.mem r cr_l) lin_prog in
    let sim_l = List.map
      (fun (r, lines) ->
        (*let lines = link_lines r lines lin_progs in*)
        r, convert_to_simplex
             (List.assoc r memories)
             (StrSet.elements (StrSet.add (List.assoc r memories) (vars_of_lines lines)))
             lines)
      (List.rev lin_prog)
    in
    let sol_l =
      List.map
        (fun (r, sim) ->
          r, -1 * (from_coef (Simplex.compute sim [List.assoc r memories, Num.Int(-1)])))
        sim_l
    in
    List.fold_left (fun out (r, n) -> out + n) 0 sol_l
  in
  let memories = List.map (fun r -> r, H.mk_pot_with_name r vars) r_l in
  let r_cost =
    List.fold_left
      (fun out r -> StrMap.add r ([], H.PPot(List.assoc r memories)) out)
      StrMap.empty r_l
  in
  saved_state := (process_t t r_cost StrMap.empty)::(!saved_state);
  let s_l = List.map (fun lp -> compute_lin_prog lp memories) !saved_state in
  let tmp = List.map (fun s -> "blabla", s) s_l in
  (* List.iter (fun (r, s) -> Printf.printf "%s:%d\n\n" r s) tmp; *)
  List.fold_left max 0 s_l

let process t =
  let r_l = StrSet.elements (rgn_of t) in
  let cr_l = StrSet.elements (concrete_rgn t) in
  process_r r_l cr_l t
