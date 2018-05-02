open Util

module S = Check
module H = No_side_effect

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
      |S.Unit |S.Bool(_) |S.Int(_) |S.Var(_) |S.Newrgn -> StrSet.empty
      |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1) |S.Hd(t1) |S.Tl(t1) |S.Nil(t1) |S.Deref(t1) |S.Freergn(t1) ->
        rgn_of t1
      |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) |S.Fun(_, _, t1, t2) |S.Let(_, t1, t2)
      |S.Letrec(_, t1, t2) |S.Ref(t1, t2) |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2) ->
        StrSet.union (rgn_of t1) (rgn_of t2)
      |S.If(t1, t2, t3) |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) ->
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
  |S.Fun(f, _, _, _) -> f
  |_ -> assert false


let from_coef c =
  match c with
  |Num.Int(out) -> out
  |_ -> assert false

let convert_coef c = Num.Int(c)

let convert_line l = List.map (fun (v, c) -> (v, convert_coef c)) l

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
    |(line, bound)::lin_prog' -> loop_line (Simplex.add_line sim (convert_line line) (Simplex.mk_const bound)) lin_prog'
  in
  loop_line (loop_var sim vars) lin_prog

let find_rgn_sub r s =
  try
    fst (List.find (fun (r1, r2) -> r2 = r) s)
  with Not_found ->
    Printf.printf "Not subs %s, should be pass ? %b\n\n" r (List.exists (fun (r1, r2) -> r1 = r) s);
    if List.exists (fun (r1, r2) -> r1 = r) s then
      raise Not_found
    else
      r

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

let vars_of_line (line, _) = List.fold_left (fun out exp -> StrSet.union (vars_of_exp exp) out) StrSet.empty line

let vars_of_lines lines = List.fold_left (fun out line -> StrSet.union (vars_of_line line) out) StrSet.empty lines

let process_r r_l t =
  let add_fun_pot env r f v = Hashtbl.add env (r, f) v in
  let find_fun_pot env r f = Hashtbl.find env (r, f) in
  let remove_fun_pot env r f = Hashtbl.remove env (r, f) in
  let env = Hashtbl.create 10 in
  let vars = ref (StrSet.empty) in
  let rec process_t t out =
  Printf.printf "--------- NO SIDE PROCCES ------------\n%s\n\n" (S.show_typed_term t);
  Printf.printf "ENV\n";
  Hashtbl.iter (fun (r, f) (c, d, lines) -> Printf.printf "%s %s : (%s, %s, %s)\n" f r c d (H.show_integer_prog lines)) env;
  Printf.printf "OUT\n";
  StrMap.iter (fun r (lines, n) -> Printf.printf "%s : %s\n%s\n" r n (H.show_integer_prog lines)) out;
  Printf.printf "\n\n";
    let te = S.get_term t in
    let ty = S.get_type t in
    match te with
    |S.Unit |S.Bool(_) |S.Int(_) -> out
    |S.Var(_) ->
      StrMap.map
        (fun (lines, n) ->
          let m = H.mk_pot vars in
          let new_line = [m, 1; n, -1], 0 in
          new_line::lines, m)
        out
    |S.Binop(_, t1, t2) |S.Comp(_, t1, t2) -> process_t t2 (process_t t1 out)
    |S.Not(t1) |S.Neg(t1) -> process_t t1 out
    |S.Fun(f, arg_l, t1, t2) ->
      if no_side_effect ty then begin
        let l_n = List.map (fun (r, (lines, n)) -> r, n) (StrMap.bindings out) in
        let l_c = List.map (fun (r, n) -> r, H.mk_pot' "c" vars) l_n in
        let l_d = List.map (fun (r, n) -> r, H.mk_pot' "d" vars) l_n in
        List.iter2 (fun (r, c) (r, d) -> add_fun_pot env r f (c, d, [])) l_c l_d;
        let out_f =
          StrMap.mapi
            (fun r (lines, d') ->
              let c = List.assoc r l_c in
              let d = List.assoc r l_d in
              if c <> d' then
                let new_line_fun = [d, 1; d', -1], 0 in
                new_line_fun::lines, d
              else
                [], c)
            (process_t t1 (StrMap.mapi (fun r (lines, n) -> [], List.assoc r l_c) out))
        in
        StrMap.iter
          (fun r (lines, d) ->
            if lines <> [] then
              add_fun_pot env r f (List.assoc r l_c, d, lines)
            else
              remove_fun_pot env r f)
          out_f
      end;
      out
    |S.App(s, t1, t_l) ->
      let out = process_t t1 out in
      let l_n' = List.map (fun (r, (lines, n)) -> r, n) (StrMap.bindings out) in
      StrMap.mapi
        (fun r (lines, n'') ->
          let new_lines =
            let n' = List.assoc r l_n' in
            try
              Printf.printf "APPICATION SUB REGION %s -> %s\n" r (find_rgn_sub r s);
              let cr, dr, fun_lines = find_fun_pot env (find_rgn_sub r s) (fun_name t1) in
              Printf.printf "APPLICATION OF %s with coef %s, %s\n" (fun_name t1) cr dr;
              ([n'', 1; cr, 1; n', -1; dr, -1], 0)::fun_lines
            with Not_found -> if n'' <> n' then [[n'', 1; n', -1], 0] else []
          in
          List.append new_lines lines, n'')
        (List.fold_left (fun out t2 -> process_t t2 out) out t_l)
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
          let m = H.mk_pot' "if" vars in
          let new_line1 = [m, 1; m2, -1], 0 in
          let new_line2 = [m, 1; m3, -1], 0 in
          new_line1::new_line2::lines, m)
        out3
    |S.Let(x, t1, t2) |S.Letrec(x, t1, t2) -> process_t t2 (process_t t1 out)
    |S.Pair(t1, t2, t3) ->
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r ty then
            let m = H.mk_pot' "pair" vars in
            let new_line = [m, 1; n, -1], -1 * (H.cost_of H.RPAIR) in
            new_line::lines, m
          else
            lines, n)
        (process_t t2 (process_t t1 out))
    |S.Fst(t1) |S.Snd(t1) |S.Hd(t1) |S.Tl(t1) |S.Nil(t1) -> process_t t1 out
    |S.Cons(t1, t2, t3) ->
      StrMap.mapi
        (fun r (lines, n) ->
          if on_rgn r ty then
            let m = H.mk_pot' "cons" vars in
            let new_line = [m, 1; n, -1], -1 * (H.cost_of H.RCONS) in
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
            let m = H.mk_pot' "hnd" vars in
            let new_line = [m, 1; n, -1], -1 * (H.cost_of H.RHND) in
            new_line::lines, m
          else
            lines, n)
        out
    |S.Aliasrgn(t1, t2) -> process_t t2 (process_t t1 out)
    |S.Freergn(t1) -> process_t t1 out
    |S.Sequence(t1, t2) -> process_t t2 (process_t t1 out)
  in
  let memories = List.map (fun r -> r, H.mk_pot' r vars) r_l in
  let lin_progs = List.fold_left (fun out r -> StrMap.add r ([], List.assoc r memories) out) StrMap.empty r_l in
  let lin_progs = process_t t lin_progs in
  let lin_progs = List.map (fun (r, (lines, _)) -> r, lines) (StrMap.bindings lin_progs) in
  let vars = StrSet.elements !vars in
  let sim_l = List.map
    (fun (r, lines) ->
      r, convert_to_simplex
           (List.assoc r memories)
           (StrSet.elements (StrSet.add (List.assoc r memories) (vars_of_lines lines)))
           lines)
    (List.rev lin_progs)
  in
  Printf.printf "ICICIICICIICICICICICICII\n\n\n\n";
  let sol_l = List.map (fun (r, sim) -> r, -1 * (from_coef (Simplex.compute sim [List.assoc r memories, Num.Int(-1)]))) sim_l in
  sol_l


let process t =
  let r_l = StrSet.elements (rgn_of t) in
  process_r r_l t
