open Util

module S = Check
module H = Analysis

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
    |S.App(_, t1, t_l) -> List.fold_left (fun out t2 -> loop t2 out) (loop t1 out) t_l
    |S.Match(t1, t2, x, xs, t3) ->
      loop t1 (loop t2 (StrSet.remove x (StrSet.remove xs (loop t3 out))))
    |S.Let(x, t1, t2) |S.Letrec(x, t1, t2) ->
      loop t1 (StrSet.remove x (loop t2 out))
  in
  let tmp = (loop t StrSet.empty) in
  Printf.printf "MARDI DEBUG : %s\n\n" (strset_str tmp);
  tmp

let rec concrete_rgn t =
  match S.get_term t with
  |S.Newrgn -> begin
    match S.get_type t with
    |S.TPoly(_, _, S.THnd(r)) -> StrSet.singleton r
    |_ -> assert false
  end
  |S.Unit |S.Bool(_) |S.Int(_) |S.Var(_) |S.Newrgn |S.Nil -> StrSet.empty
  |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1) |S.Hd(t1) |S.Tl(t1) |S.Deref(t1) |S.Freergn(t1) ->
    concrete_rgn t1
  |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) |S.Fun(_, _, t1, t2, _) |S.Let(_, t1, t2)
  |S.Letrec(_, t1, t2) |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2) ->
    StrSet.union (concrete_rgn t1) (concrete_rgn t2)
  |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) |S.Match(t1, t2, _, _, t3) ->
    StrSet.union (concrete_rgn t1) (StrSet.union (concrete_rgn t2) (concrete_rgn t3))
  |S.App(_, t1, t_l) ->
    List.fold_left (fun out t2 -> StrSet.union (concrete_rgn t2) out) (concrete_rgn t1) t_l

let rec rgn_mty mty =
  match mty with
  |S.TInt |S.TBool |S.TUnit |S.TAlpha(_) -> StrSet.empty
  |S.TList(mty1, r) |S.TRef(mty1, r) -> StrSet.add r (rgn_mty mty1)
  |S.TCouple(mty1, mty2, r) -> StrSet.add r (StrSet.union (rgn_mty mty1) (rgn_mty mty2))
  |S.TFun(mty_l, mty2, r, _, _, _) ->
    List.fold_left (fun out mty1 -> StrSet.union (rgn_mty mty1) out) (StrSet.add r (rgn_mty mty2)) mty_l
  |S.THnd(r) -> StrSet.singleton r

let rgn_ty (S.TPoly(_, _, mty)) = rgn_mty mty

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
      |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) |S.Match(t1, t2, _, _, t3) ->
        StrSet.union (rgn_of t1) (StrSet.union (rgn_of t2) (rgn_of t3))
      |S.App(_, t1, t_l) ->
        List.fold_left (fun out t2 -> StrSet.union (rgn_of t2) out) (rgn_of t1) t_l
    )
    (rgn_ty (S.get_type t))

let on_rgn r (S.TPoly(_, _, mty)) =
  match mty with
  |S.TInt |S.TBool |S.TUnit |S.TAlpha(_) -> false
  |S.TFun(_, _, r', _, _, _) |S.TCouple(_, _, r') |S.TList(_, r') |S.TRef(_, r') |S.THnd(r') -> r = r'

let fun_name t =
  match S.get_term t with
  |S.Var(v) -> v
  |S.Fun(f, _, _, _, _) -> f
  |_ -> assert false


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
  |S.TPoly(_, _, S.TFun(_, _, _, _, _, phi)) ->
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

let get_rgn (S.TPoly(_, _, mty)) =
  match mty with
  |S.TInt |S.TBool |S.TUnit |S.TAlpha(_) -> assert false
  |S.TFun(_, _, r, _, _, _) |S.TCouple(_, _, r)
  |S.TList(_, r) |S.TRef(_, r) |S.THnd(r) -> r

let rec instanciate_size p t_l out =
  match p with
  |H.PPot(_) |H.PLit(_) -> p, out
  |H.PSize(i) ->
    let rec loop t_l i =
      match t_l with
      |[] -> H.PUnit, out
      |hd::tl ->
        let ty = S.get_type hd in
        if i = 0 then
          let r = get_rgn ty in
          H.PPot(r), r::out
        else
          loop tl (i-1)
    in loop t_l i
  |H.PAdd(p1, p2) ->
    let p1', out = instanciate_size p1 t_l out in
    let p2', out = instanciate_size p2 t_l out in
    H.PAdd(p1', p2'), out
  |H.PMin(p1) ->
    let p1', out = instanciate_size p1 t_l out in
    H.PMin(p1'), out
  |H.PMul(p1, p2) ->
    let p1', out = instanciate_size p1 t_l out in
    let p2', out = instanciate_size p2 t_l out in
    H.PMul(p1', p2'), out
  |H.PUnit -> H.PUnit, out

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
(*
let rec verify_r f arg_l (r, (pc, pd)) t =
  match t with
  |S.Unit
  |S.Bool(b)
  |S.Int(i)
  |S.Var(v)
  |S.Binop(op, t1, t2)
  |S.Not(t1)
  |S.Neg(t1)
  |S.Comp(c, t1, t2)
  |S.Fun(ff, f_arg_l, t1, t2, f_pot)
  |S.App(_, t1, t_l)
  |S.If(t1, t2, t3)
  |S.Match(t_match, t_nil, x, xs, t_cons)
  |S.Let(_, t1, t2)
  |S.Letrec (_, t1, t2)
  |S.Pair(t1, t2, t3)
  |S.Fst(t1)
  |S.Snd(t1)
  |S.Hd(t1)
  |S.Tl(t1)
  |S.Nil(t1)
  |S.Cons(t1, t2, t3)
  |S.Ref(t1, t2)
  |S.Assign(t1, t2)
  |S.Deref(t1)
  |S.Newrgn
  |S.Aliasrgn(t1, t2)
  |S.Freergn(t1)
  |S.Sequence(t1, t2)
*)

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
  let rec process_t t out =
(*  Printf.printf "--------- NO SIDE PROCCES ------------\n%s\n\n" (S.show_typed_term t);
  Printf.printf "ENV\n";
  Hashtbl.iter (fun (r, f) (c, d, lines) -> Printf.printf "%s %s : (%s, %s, %s)\n" f r c d (H.show_integer_prog lines)) env;
  Printf.printf "OUT\n";
  StrMap.iter (fun r (lines, n) -> Printf.printf "%s : %s\n%s\n" r n (H.show_integer_prog lines)) out;
  Printf.printf "\n\n";*)
    let te = S.get_term t in
    let ty = S.get_type t in
    match te with
    |S.Unit |S.Bool(_) |S.Int(_) |S.Nil -> out
    |S.Var(_) ->
      StrMap.map
        (fun (lines, n) ->
          let m = H.PPot(H.mk_pot vars) in
          let new_line = H.PAdd(m, H.PMin  n) in
          new_line::lines, m)
        out
    |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) -> process_t t2 (process_t t1 out)
    |S.Not(t1) |S.Neg(t1) -> process_t t1 out
    |S.Fun(f, arg_l, t1, t2, pot) when no_side_effect ty -> begin
      let out =
        StrMap.mapi
          (fun r (lines, n) ->
            if on_rgn r ty then
              let m = H.PPot(H.mk_pot' "fun" vars) in
              let fv_var = fv_term t1 in
              let nb_fv = StrSet.cardinal (StrSet.remove f (List.fold_left (fun out arg -> StrSet.remove arg out) fv_var arg_l)) in
              let const = nb_fv * (H.cost_of H.RCLO) in
              let new_line = H.PAdd(H.PAdd(m, H.PMin n), H.PLit(nb_fv * (H.cost_of H.RCLO))) in
              new_line::lines, m
            else
              lines, n)
          out
      in
      match pot with
      |Some(fun_pot_l) ->
        List.iter (fun (r, (pc, pd)) -> add_fun_pot r f (pc, pd, [])) fun_pot_l;
        out
      |None ->
        let l_n = List.map (fun (r, (lines, n)) -> r, n) (StrMap.bindings out) in
        let l_c = List.map (fun (r, n) -> r, H.PPot(H.mk_pot' "c" vars)) l_n in
        let l_d = List.map (fun (r, n) -> r, H.PPot(H.mk_pot' "d" vars)) l_n in
        List.iter2 (fun (r, c) (r, d) -> add_fun_pot r f (c, d, [])) l_c l_d;
        let out_f =
          StrMap.mapi
            (fun r (lines, d') ->
              let c = List.assoc r l_c in
              let d = List.assoc r l_d in
              if c <> d' then
                let new_line_fun = H.PAdd(d, H.PMin d') in
                new_line_fun::lines, d
              else
                [], c)
            (process_t t1 (StrMap.mapi (fun r (lines, n) -> [], List.assoc r l_c) out))
        in
        StrMap.iter
          (fun r (lines, d) ->
            if lines <> [] then
              add_fun_pot r f (List.assoc r l_c, d, lines)
            else
              remove_fun_pot r f)
          out_f;
        out
    end
    |S.App(s, t1, t_l) ->
      let out = process_t t1 out in
      let l_n' = List.map (fun (r, (lines, n')) -> r, n') (StrMap.bindings out) in
      let out = List.fold_left (fun out t2 -> process_t t2 out) out t_l in
      StrMap.mapi
        (fun r (lines, n'') ->
          let new_lines, n'' =
            let n' = List.assoc r l_n' in
            try
              let r_sub_l = List.filter (fun r_sub -> mem_fun_pot r_sub (fun_name t1)) (find_rgn_sub r s) in
              Printf.printf "APPICATION SUB REGION %s -> %s\n" r ("[" ^ (List.fold_left (fun out r -> Printf.sprintf "%s, %s" out r) "" r_sub_l) ^ "]");
              let out1, n', n'' = List.fold_left
                (fun (out1, n', n'') r_sub ->
                  let cr, dr, fun_lines = find_fun_pot r_sub (fun_name t1) in
                  let cr', r_cr' = instanciate_size cr t_l [] in
                  let dr', r_dr' = instanciate_size dr t_l [] in
                  let fun_lines, sub =
                    fresh_names
                      (
                        List.fold_left
                          (fun fun_lines r ->
                            let rlines, _ = StrMap.find r out in
                            List.rev_append rlines fun_lines)
                          fun_lines
                          (List.rev_append r_cr' r_dr')
                      ) vars StrMap.empty
                  in
                  let cr'', sub = fresh_names_p cr' vars sub in
                  let dr'', sub = fresh_names_p dr' vars sub in
                  Printf.printf "APPLICATION OF %s with coef %s, %s\n" (fun_name t1) (H.show_pot cr'') (H.show_pot dr'');
                  (List.rev_append ((H.PAdd(H.PAdd(H.PAdd(n'', cr''), H.PMin n'), H.PMin dr''))::fun_lines) out1,
                  n'',
                  H.PPot(H.mk_pot vars)))
                ([], n', n'')
                r_sub_l
              in
              out1, n'
            with Not_found -> if n'' <> n' then [H.PAdd(n'', H.PMin n')], n'' else [], n''
          in
          List.append new_lines lines, n'')
        out
    |S.If(t1, t2, t3) ->
      let out1 = process_t t1 out in
      let l_n1 = List.map (fun (r, (lines, n)) -> r, n) (StrMap.bindings out1) in
      let out2 = process_t t2 out1 in
      let l_n2 = List.map (fun (r, (lines, n)) -> r, n) (StrMap.bindings out2) in
      let out2' = StrMap.mapi (fun r (lines, _) -> lines, List.assoc r l_n1) out2 in
      let out3 = process_t t3 out2' in
      StrMap.mapi
        (fun r (lines, m3) ->
          let m2 = List.assoc r l_n2 in
          let m = H.PPot(H.mk_pot' "if" vars) in
          let new_line1 = H.PAdd(m, H.PMin m2) in
          let new_line2 = H.PAdd(m, H.PMin m3) in
          new_line1::new_line2::lines, m)
        out3
    |S.Match(t_match, t_nil, x, xs, t_cons) -> assert false
    |S.Let(x, t1, t2) |S.Letrec(x, t1, t2) -> process_t t2 (process_t t1 out)
    |S.Pair(t1, t2, t3) ->
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r ty then
            let m = H.PPot(H.mk_pot' "pair" vars) in
            let new_line = H.PAdd(H.PAdd(m, H.PMin n), H.PLit(H.cost_of H.RPAIR)) in
            new_line::lines, m
          else
            lines, n)
        (process_t t2 (process_t t1 out))
    |S.Fst(t1) |S.Snd(t1) |S.Hd(t1) |S.Tl(t1) -> process_t t1 out
    |S.Cons(t1, t2, t3) ->
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r ty then
            let m = H.PPot(H.mk_pot' "cons" vars) in
            let new_line = H.PAdd(H.PAdd(m, H.PMin n), H.PLit(H.cost_of H.RCONS)) in
            new_line::lines, m
          else
            lines, n)
        (process_t t2 (process_t t1 out))
    |S.Ref(t1, t2) -> process_t t2 (process_t t1 out)
    |S.Assign(t1, t2) -> process_t t2 (process_t t1 out)
    |S.Deref(t1) -> process_t t1 out
    |S.Newrgn ->
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r ty then
            let m = H.PPot(H.mk_pot' "hnd" vars) in
            let new_line = H.PAdd(H.PAdd(m, H.PMin n), H.PLit(H.cost_of H.RHND)) in
            new_line::lines, m
          else
            lines, n)
        out
    |S.Aliasrgn(t1, t2) -> process_t t2 (process_t t1 out)
    |S.Freergn(t1) -> process_t t1 out
    |S.Sequence(t1, t2) -> process_t t2 (process_t t1 out)
  in
  let memories = List.map (fun r -> r, H.mk_pot_with_name r vars) r_l in
  let lin_progs = List.fold_left (fun out r -> StrMap.add r ([], H.PPot(List.assoc r memories)) out) StrMap.empty r_l in
  let lin_progs = process_t t lin_progs in
  let lin_progs = List.map (fun (r, (lines, _)) -> r, lines) (StrMap.bindings lin_progs) in
  let lin_progs = List.filter (fun (r, lines) -> List.mem r cr_l) lin_progs in
  let vars = StrSet.elements !vars in
  let sim_l = List.map
    (fun (r, lines) ->
      (*let lines = link_lines r lines lin_progs in*)
      r, convert_to_simplex
           (List.assoc r memories)
           (StrSet.elements (StrSet.add (List.assoc r memories) (vars_of_lines lines)))
           lines)
    (List.rev lin_progs)
  in
  Printf.printf "ICICIICICIICICICICICICII\n\n\n\n";
  print_fun_pot ();
  let sol_l = List.map (fun (r, sim) -> r, -1 * (from_coef (Simplex.compute sim [List.assoc r memories, Num.Int(-1)]))) sim_l in
  sol_l


let process t =
  let r_l = StrSet.elements (rgn_of t) in
  let cr_l = StrSet.elements (concrete_rgn t) in
  process_r r_l cr_l t
