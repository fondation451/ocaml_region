open Util

module S = Simpl
module T = Check

(*let rec unlift_type = function
  | T.TInt -> S.TInt
  | T.TBool -> S.TBool
  | T.TUnit -> S.TUnit
  | T.TAlpha a -> S.TAlpha a
  | T.TFun (_, mty_l, mty1, r, _, _, _) -> S.TFun (List.map unlift_type mty_l, unlift_type mty1, r)
  | T.TCouple (mty1, mty2, r) -> S.TCouple (unlift_type mty1, unlift_type mty2, r)
  | T.TList (ls, mty1, r) -> S.TList (ls, unlift_type mty1, r)
  | T.TTree (lsn, lsd, mty1, r) -> S.TTree (lsn, lsd, unlift_type mty1, r)
  | T.TRef (i, mty1, r) -> S.TRef (i, unlift_type mty1, r)
  | T.THnd r -> S.THnd r
*)
let rec lift_type mty =
  match mty with
  |S.TInt -> T.TInt
  |S.TBool -> T.TBool
  |S.TUnit -> T.TUnit
  |S.TAlpha(a) -> T.TAlpha(a)
  |S.TFun(mty_l, mty1, r) ->
    T.TFun(
      [],
      List.map lift_type mty_l,
      lift_type mty1,
      r,
      T.empty_capabilities,
      T.empty_capabilities,
      T.empty_effects
    )
  |S.TCouple(mty1, mty2, r) -> T.TCouple(lift_type mty1, lift_type mty2, r)
  |S.TList(i, mty1, r) -> T.TList(i, lift_type mty1, r)
  |S.TTree(lsn, lsd, mty1, r) -> T.TTree(lsn, lsd, lift_type mty1, r)
  |S.TRef(id, mty1, r) -> T.TRef(id, lift_type mty1, r)
  |S.THnd(r) -> T.THnd(r)

let fv_mty mty =
  let rec loop mty out =
    match mty with
    |T.TInt |T.TBool |T.TUnit |T.THnd(_) -> out
    |T.TAlpha(a) -> StrSet.add a out
    |T.TFun(_, mty_l, mty1, r, cin, cout, phie) ->
      List.fold_left (fun out mty -> loop mty out) (loop mty1 out) mty_l
    |T.TCouple(mty1, mty2, r) -> loop mty1 (loop mty2 out)
    |T.TList(_, mty1, r) |T.TTree(_, _, mty1, r) |T.TRef(_, mty1, r) -> loop mty1 out
  in loop mty StrSet.empty

let fr_mty mty =
  let rec loop mty out =
    match mty with
    |T.TInt |T.TBool |T.TUnit |T.TAlpha(_) -> out
    |T.THnd(r) -> StrSet.add r out
    |T.TFun(_, mty_l, mty1, r, cin, cout, phie) ->
      List.fold_left (fun out mty -> loop mty out) (loop mty1 (StrSet.add r out)) mty_l
    |T.TCouple(mty1, mty2, r) -> loop mty1 (loop mty2 (StrSet.add r out))
    |T.TList(_, mty1, r) |T.TTree(_, _, mty1, r) |T.TRef(_, mty1, r) -> loop mty1 (StrSet.add r out)
  in loop mty StrSet.empty

let unrestricted c g = T.cap_forall (fun (r, cap) -> not (T.gamma_mem r g) || (cap = T.Relaxed)) c

let sub_cap c1 c2 =
  T.cap_forall
    (fun (r, p) ->
      (p = T.Relaxed && T.cap_relaxed r c1) ||
      (p = T.Linear && T.cap r c1))
    c2

(* Construction CIN *)
let rec rgn_of t =
  let merge_rgn _ _ _ = Some(T.Relaxed) in
  match S.get_term t with
  |S.Unit |S.Bool(_) |S.Int(_) |S.Var(_) |S.Newrgn |S.Nil |S.Leaf -> StrMap.empty
  |S.Not(t1) |S.Neg(t1) |S.Fst(t1) |S.Snd(t1) |S.Hd(t1)
  |S.Tl(t1) |S.Deref(t1) |S.Freergn(t1) ->
    rgn_of t1
  |S.Let(_, t1, t2) |S.Letrec(_, t1, t2) |S.Binop(_, t1, t2) |S.Comp(_, t1, t2)
  |S.Assign(t1, t2) |S.Aliasrgn(t1, t2) |S.Sequence(t1, t2) ->
    StrMap.union merge_rgn (rgn_of t1) (rgn_of t2)
  |S.If(t1, t2, t3) ->
    StrMap.union merge_rgn (rgn_of t1) (StrMap.union merge_rgn (rgn_of t2) (rgn_of t3))
  |S.MatchList(var_match, t2, _, _, t3) |S.MatchTree(var_match, t2, _, _, _, t3) ->
    StrMap.union merge_rgn (rgn_of t2) (rgn_of t3)
  |S.App(t1, arg_l) -> rgn_of t1
  |S.Fun(_, _, t1, t2, _) |S.Ref(t1, t2) ->
    StrMap.union
      merge_rgn
      (rgn_of t1)
      (match S.get_type t2 with
       |S.THnd(r) -> StrMap.singleton r T.Relaxed
       |_ -> assert false)
  |S.Pair(t1, t2, t3) |S.Cons(t1, t2, t3) ->
    StrMap.union
      merge_rgn
      (rgn_of t1)
      (StrMap.union
        merge_rgn
        (rgn_of t2)
        (match S.get_type t3 with
         |S.THnd(r) -> StrMap.singleton r T.Relaxed
         |_ -> assert false))
  |S.Node(t1, t2, t3, t4) ->
    StrMap.union
      merge_rgn
      (rgn_of t1)
      (StrMap.union
          merge_rgn
          (rgn_of t2)
          (StrMap.union
            merge_rgn
            (rgn_of t3)
            (match S.get_type t4 with
              |S.THnd(r) -> StrMap.singleton r T.Relaxed
              |_ -> assert false)))
(* **** *)

let generalize_cap c c_ref =
  T.cap_map (fun (r, cap) -> (r, try T.cap_find r c_ref with Not_found -> cap)) c


(* Instanciation of regions in application *)
let merge_some s1 s2 =
  match s1, s2 with
  |None, None -> None
  |Some(out), None |None, Some(out) -> Some(out)
  |Some(out1), Some(out2) -> if out1 = out2 then Some(out1) else assert false

let replace s r = try StrMap.find r s with Not_found -> r
let replace_cap s c = T.cap_map (fun (r, p) -> (replace s r, p)) c
let replace_effects s phi =
  T.effects_map
    (fun e ->
      match e with
      |T.ERead(r) -> T.ERead(replace s r)
      |T.EWrite(r) -> T.EWrite(replace s r)
      |T.EAlloc(r) -> T.EAlloc(replace s r))
    phi

let rec replace_rgn s mty =
  match mty with
  |T.TInt|T.TBool |T.TUnit |T.TAlpha(_) -> mty
  |T.THnd(r) -> T.THnd(replace s r)
  |T.TFun(s', arg_l, mty1, r, cin, cout, phie) ->
    T.TFun
      (
        List.map (fun (r1, r2) -> (replace s r1, replace s r2)) s',
        List.map (replace_rgn s) arg_l,
        replace_rgn s mty1,
        replace s r,
        replace_cap s cin,
        replace_cap s cout,
        replace_effects s phie
      )
  |T.TCouple(mty1, mty2, r) -> T.TCouple(replace_rgn s mty1, replace_rgn s mty2, replace s r)
  |T.TList(i, mty1, r) -> T.TList(i, replace_rgn s mty1, replace s r)
  |T.TTree(lsn, lsd, mty1, r) -> T.TTree(lsn, lsd, replace_rgn s mty1, replace s r)
  |T.TRef(id, mty1, r) -> T.TRef(id, replace_rgn s mty1, replace s r)

let rec instance_of_rgn r mty1 mty2 =
  match mty1, mty2 with
  |T.TInt, T.TInt |T.TBool, T.TBool |T.TUnit, T.TUnit
  |T.TAlpha(_), T.TAlpha(_) |T.TAlpha(_), _ |_, T.TAlpha(_) -> None
  |T.THnd(r1), T.THnd(r2) ->
    if r1 = r then
      Some(r2)
    else
      None
  |T.TFun(_, arg_l1, dst1, r1, _, _, _), T.TFun(_, arg_l2, dst2, r2, _, _, _) ->
    if r1 = r then
      Some(r2)
    else
      List.fold_left2
        (fun out arg1 arg2 -> merge_some (instance_of_rgn r arg1 arg2) out)
        (instance_of_rgn r dst1 dst2)
        arg_l1
        arg_l2
  |T.TCouple(mty1, mty2, r1), T.TCouple(mty1', mty2', r2) ->
    if r1 = r then
      Some(r2)
    else
      merge_some (instance_of_rgn r mty1 mty1') (instance_of_rgn r mty2 mty2')
  |T.TList(_, mty1, r1), T.TList(_, mty1', r2)
  |T.TTree(_, _, mty1, r1), T.TTree(_, _, mty1', r2)
  |T.TRef(_, mty1, r1), T.TRef(_, mty1', r2) ->
    if r = r1 then
      Some(r2)
    else
      instance_of_rgn r mty1 mty1'
  |_ ->
    raise (T.Error(Printf.sprintf "instance_of_rgn %s %s %s" r
                                  (T.show_rcaml_type mty1)
                                  (T.show_rcaml_type mty2)))

let instance_of_rgn_l r_l mty1 mty2 =
  let s = List.fold_left
            (fun out r ->
              match instance_of_rgn r mty1 mty2 with
              |Some(r') -> StrMap.add r r' out
              |None -> out)
            StrMap.empty r_l
  in
  let r_proceed = List.map fst (StrMap.bindings s) in
  List.filter (fun r -> not (List.mem r r_proceed)) r_l, s

let rec instance_of_rgn_mty_l r_l mty1_l mty2_l =
  let rec loop r_l mty1_l mty2_l out =
    if r_l = [] then
      [], out
    else begin
      match mty1_l, mty2_l with
      |[], [] -> r_l, out
      |mty1::mty1_l', mty2::mty2_l' ->
        let r_l', s = instance_of_rgn_l r_l mty1 mty2 in
        loop r_l' mty1_l' mty2_l' (StrMap.union (fun _ r1 r2 -> Some(r1)) s out)
      |_ -> assert false
    end
  in loop r_l mty1_l mty2_l StrMap.empty

let inst_mty r_l f_mty arg_ty_l =
  match f_mty with
  |T.TFun(_, mty_l, mty1, mty2, cin, cout, phie) ->
    let r_l', s = instance_of_rgn_mty_l r_l mty_l arg_ty_l in
    r_l', s
  |_ -> assert false
(* **** *)

let str_of_cap cap =
  match cap with
  |T.Linear -> "1"
  |T.Relaxed -> "+"

let print_cap c name =
  Printf.printf "%s : \n%s\n"
    name
    ("[" ^ (List.fold_left (fun out (r, cap) -> Printf.sprintf "%s, (%s, %s)" out r (str_of_cap cap)) "" c) ^ "]")

let print_gamma g name =
  Printf.printf "%s : \n%s\n"
    name
    ("[" ^ (List.fold_left (fun out r -> Printf.sprintf "%s, %s" out r) "" g) ^ "]")

let rec rgn_subs mty1 mty2 out =
  match mty1, mty2 with
  |S.TFun(mty_l, mty2, r), T.TFun(_, mty_l', mty2', r', cin, cout, phi) ->
    List.fold_left2
      (fun out mty1 mty1' -> rgn_subs mty1 mty1' out)
      (rgn_subs mty2 mty2' (StrMap.add r' r out))
      mty_l mty_l'
  |S.TCouple(mty1, mty2, r), T.TCouple(mty1', mty2', r') ->
    rgn_subs mty1 mty1' (rgn_subs mty2 mty2' (StrMap.add r' r
     out))
  |S.TList(_, mty1, r), T.TList(_, mty1', r')
  |S.TTree(_, _, mty1, r), T.TTree(_, _, mty1', r')
  |S.TRef(_, mty1, r), T.TRef(_, mty1', r') ->
    rgn_subs mty1 mty1' (StrMap.add r' r out)
  |S.THnd(r), T.THnd(r') -> StrMap.add r' r out
  |_ -> out

let rec merge_mty mty_out mty_checked =
  match mty_out, mty_checked with
  |S.TFun(mty_l, mty2, r), T.TFun(_, mty_l', mty2', _, cin, cout, phi) ->
    let s =
      List.fold_left2
        (fun out mty1 mty1' -> rgn_subs mty1 mty1' out)
        (rgn_subs mty2 mty2' StrMap.empty)
        mty_l mty_l'
    in
    (* Printf.printf "DEBUG\n";
    List.iter (fun (r1, r2) -> Printf.printf "(%s, %s) ; " r1 r2) (StrMap.bindings s);
    Printf.printf "\n////DEBUG\n";
    print_cap cin "cin";
    print_cap (replace_cap s cin) "cin'";
    print_cap cout "cout";
    print_cap (replace_cap s cout) "cout'"; *)
    T.TFun(
      StrMap.bindings s,
      List.map2 merge_mty mty_l mty_l',
      merge_mty mty2 mty2',
      r,
      replace_cap s cin,
      replace_cap s cout,
      replace_effects s phi
    )
  |S.TCouple(mty1, mty2, r), T.TCouple(mty1', mty2', _) ->
    T.TCouple(merge_mty mty1 mty1', merge_mty mty2 mty2', r)
  |S.TList(ls, mty1, r), T.TList(_, mty1', _) ->
    T.TList(ls, merge_mty mty1 mty1', r)
  |S.TTree(lsn, lsd, mty1, r), T.TTree(_, _, mty1', _) ->
    T.TTree(lsn, lsd, merge_mty mty1 mty1', r)
  |S.TRef(id, mty1, r), T.TRef(_, mty1', _) ->
    T.TRef(id, merge_mty mty1 mty1', r)
  |S.THnd(r), T.THnd(r') -> T.THnd(r)
  |S.TInt, _ -> T.TInt
  |S.TBool, _ -> T.TBool
  |S.TUnit, _ -> T.TUnit
  |S.TAlpha(a), _ -> T.TAlpha(a)
  |_ -> mty_checked


let check_rgn r c =
  (* Printf.printf "CHECK_RGN OF %s !!!!!\n\n" r; *)
  if T.cap_linear r c then
    T.remove_cap r c, T.effects_of [T.ERead(r)]
  else if T.cap_relaxed r c then
    c, T.effects_of [T.ERead(r)]
  else
    raise (T.Error (Printf.sprintf "No capabilities for region handler %s" r))

let rec check_term env g c t =
  let te = S.get_term t in
  let mty = S.get_type t in
  let a_l = S.get_alpha_l t in
  let r_l = S.get_rgn_l t in

   print_cap c "c";
  Printf.printf "--------- CHECK PROCCES ------------\n%s\n\n" (S.show_typed_term t); 
  (* let te = S.get_term t in
  let S.TPoly(a_l, r_l, ty) = S.get_type t in *)
  let g' = List.fold_left (fun out r -> T.gamma_add r out) g r_l in
  let (te', mty', g_out, c_out, phi_out) =
    match te, mty with
    |S.Unit, S.TUnit -> T.Unit, T.TUnit, g, c, T.empty_effects
    |S.Bool(b), S.TBool -> T.Bool(b), T.TBool, g, c, T.empty_effects
    |S.Int(i), S.TInt -> T.Int(i), T.TInt, g, c, T.empty_effects
    |S.Var(v), _ -> begin
      Printf.printf "CHECKING OF %s\n\n" (S.show_typed_term t);
      StrMap.iter
        (fun x mty_x -> Printf.printf "  %s : %s\n" x (T.show_rcaml_type mty_x))
        env;
      print_cap c "VAR__c";
      print_gamma g "VAR__g"; 
(*      let mty' = try StrMap.find v env with Not_found -> lift_type mty in*)
      let mty' =
        match mty with
        | S.TFun (_, _, _) -> (try StrMap.find v env with Not_found -> lift_type mty)
        | _ -> lift_type mty
      in
(*      Printf.printf "TYPE %s\n\n\n" (T.show_rcaml_type mty'); *)
      match mty' with
      |T.THnd(r) |T.TFun(_, _, _, r, _, _, _) |T.TCouple(_, _, r) |T.TList(_, _, r) |T.TRef(_, _, r) ->
        if T.gamma_mem r g' then
          T.Var(v), mty', g, c, T.effects_of [T.ERead(r)]
        else
          raise (T.Error (Printf.sprintf "No capabilities for access to region %s" r))
      |_ -> T.Var(v), mty', g, c, T.empty_effects
    end
    |S.Binop(op, t1, t2), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      let phi = T.merge_effects phi1 phi2 in
      T.Binop(op, t1', t2'), lift_type mty, g2, c2, phi
    |S.Not(t1), S.TBool ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      T.Not(t1'), T.TBool, g1, c1, phi1
    |S.Neg(t1), S.TInt ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      T.Neg(t1'), T.TInt, g1, c1, phi1
    |S.Comp(comp, t1, t2), S.TBool ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      let phi = T.merge_effects phi1 phi2 in
      T.Comp(comp, t1', t2'), T.TBool, g2, c2, phi
    |S.Fun(f, arg_l, t1, t2, pot), S.TFun(mty_l, mty1, r) ->
      let t2', g2, c2, phi2 = check_term env g c t2 in
      let c3, phi3 = check_rgn r c2 in
      let env' =
        List.fold_left2
          (fun out x mty ->
            let mty' = lift_type mty in
            StrMap.add x mty' out)
        env arg_l mty_l
      in
      let cin = T.cap_of_strmap (rgn_of t1) in
      (* print_cap cin "cin"; *)
      let t1', g1, cout, phi_f = check_term env' g2 cin t1 in
      (* print_cap cout "cout"; *)
      let cin' = T.diff_cap cin (T.cap_of r_l) in
      (* print_cap cin' "cin'"; *)
      let cout' = T.diff_cap cout (T.cap_of r_l) in
      (* print_cap cout' "cout'"; *)
      if unrestricted cin g2 then
        T.Fun(f, arg_l, t1', t2', pot),
        T.TFun([], List.map lift_type mty_l, lift_type mty1, r, cin, cout, phi_f),
        g2, c3,
        T.merge_effects (T.merge_effects (T.effects_of [T.EAlloc(r)]) phi2) phi3
      else
        raise (T.Error (Printf.sprintf "Error with function region behaviour %s" r))
    |S.App(t1, arg_l), _ -> begin
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t_l' = List.map (fun arg ->
      Printf.printf "App %s\n" arg;
      T.mk_term (T.Var arg) (StrMap.find arg env) [] []) arg_l in
(*      let t_l', g2, c2, phi2 =
        let rec loop g c t_l =
          match t_l with
          |[] -> [], g, c, T.empty_effects
          |head::tail ->
            let head', g', c', phi' = check_term env g c head in
            let t_l_out, g_out, c_out, phi_out = loop g' c' tail in
            head'::t_l_out, g_out, c_out, T.merge_effects phi' phi_out
        in loop g1 c1 t_l
      in*)
      (* let r_l', s = inst_mty r_l (T.get_type t1') (List.map T.get_type t_l') in *)
      (* let s' = StrMap.bindings s in *)
      (* let t1_mty'' = replace_rgn s (T.get_type t1') in *)
      (* let t1'' = T.mk_term (T.get_term t1') t1_mty'' a_l r_l' in
      Printf.printf "AAAAAAAAAAAAAAAQQQQQQQQQQQQQQQQUUUUUUUUUUUUUUUUUIIIIIIIIIIIIIIIII %s\n\n\n\n\n" (T.show_rcaml_type t1_mty''); *)
      match T.get_type t1' with
      |T.TFun(_, arg_mty_l, mty_res, mty_r, cin, cout, phie) as f_mty ->
        (* print_cap c2 "c2";
        print_cap cin "cin";
        print_cap cout "cout"; *)
  (*      let new_f_ty = inst_ty f_ty (List.map T.get_type t_l') in*)
        if sub_cap c1 cin then
          T.App(t1', t_l'),
          lift_type mty,
          g1,
          T.union_cap (T.diff_cap c1 (T.diff_cap cin cout)) (T.diff_cap cout cin),
          T.merge_effects phie phi1
        else
          raise (T.Error (Printf.sprintf "Function call : capabilities not sub cap of cin"))
      |_ -> assert false
    end
    |S.If(t1, t2, t3), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      let t3', g3, c3, phi3 = check_term env g1 c1 t3 in
      T.If(t1', t2', t3'), lift_type mty, g3, c3, T.merge_effects phi1 (T.merge_effects phi2 phi3)
    |S.MatchList(var_match, t_nil, x, xs, t_cons), _ ->
      let mty_match = StrMap.find var_match env in
      let T.TList (ls, mty_x, r) = mty_match in
      let t_match = T.mk_term (T.Var var_match) mty_match [] [] in
      let t_nil', g2, c2, phi2 = check_term env g c t_nil in
      let env' = StrMap.add x mty_x (StrMap.add xs mty_match env) in
      let t_cons', g3, c3, phi3 = check_term env' g c t_cons in
      T.MatchList(t_match, t_nil', x, xs, t_cons'), lift_type mty,
      g3, c3, T.merge_effects phi2 phi3
    |S.MatchTree(var_match, t_leaf, x, tl, tr, t_node), _ ->
      let mty_match = StrMap.find var_match env in
      let T.TTree (lsn, lsd, mty_x, r) = mty_match in
      let t_match = T.mk_term (T.Var var_match) (StrMap.find var_match env) [] [] in
      let t_leaf', g2, c2, phi2 = check_term env g c t_leaf in
      let env' = StrMap.add x mty_x (StrMap.add tl mty_match (StrMap.add tr mty_match env)) in
      let t_node', g3, c3, phi3 = check_term env' g c t_node in
      T.MatchTree(t_match, t_leaf', x, tl, tr, t_node'), lift_type mty,
      g3, c3, T.merge_effects phi2 phi3
    |S.Let(x, t1, t2), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term (StrMap.add x (T.get_type t1') env) g1 c1 t2 in
      T.Let(x, t1', t2'), lift_type mty, g2, c2, T.merge_effects phi1 phi2
    |S.Letrec(x, t1, t2), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let env' = StrMap.add x (T.get_type t1') env in
      let t1', g1, c1, phi1 = check_term env' g c t1 in
      let t2', g2, c2, phi2 = check_term env' g1 c1 t2 in
      T.Letrec(x, t1', t2'), lift_type mty, g2, c2, T.merge_effects phi1 phi2
    |S.Pair(t1, t2, t3), S.TCouple(_, _, r) ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      let t3', g3, c3, phi3 = check_term env g2 c2 t3 in
      let c4, phi4 = check_rgn r c3 in
      let phi = T.merge_effects phi4 (T.merge_effects phi1 (T.merge_effects phi2 phi3)) in
      T.Pair(t1', t2', t3'), lift_type mty, g3, c4, phi
    |S.Fst(t1), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      T.Fst(t1'), lift_type mty, g1, c1, phi1
    |S.Snd(t1), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      T.Snd(t1'), lift_type mty, g1, c1, phi1
    |S.Hd(t1), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      T.Hd(t1'), lift_type mty, g1, c1, phi1
    |S.Tl(t1), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      T.Tl(t1'), lift_type mty, g1, c1, phi1
    |S.Nil, S.TList(_, _, r) -> T.Nil, lift_type mty, g, c, T.empty_effects
    |S.Leaf, S.TTree(_, _, _, _) -> T.Leaf, lift_type mty, g, c, T.empty_effects
    |S.Cons(t1, t2, t3), S.TList(_, _, r) ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      let t3', g3, c3, phi3 = check_term env g2 c2 t3 in
      let c4, phi4 = check_rgn r c3 in
      let phi = T.merge_effects phi4 (T.merge_effects phi1 (T.merge_effects phi2 phi3)) in
      T.Cons(t1', t2', t3'), lift_type mty, g3, c4, phi
    |S.Node(t1, t2, t3, t4), S.TTree(_, _, _, r) ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      let t3', g3, c3, phi3 = check_term env g2 c2 t3 in
      let t4', g4, c4, phi4 = check_term env g3 c3 t4 in
      let c5, phi5 = check_rgn r c4 in
      let phi = T.merge_effects phi5 (T.merge_effects phi4 (T.merge_effects phi1 (T.merge_effects phi2 phi3))) in
      T.Node(t1', t2', t3', t4'), lift_type mty, g4, c5, phi
    |S.Ref(t1, t2), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      let phi = T.merge_effects phi1 phi2 in
      T.Ref(t1', t2'), lift_type mty, g2, c2, phi
    |S.Assign(t1, t2), S.TUnit ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      let (T.TRef(_, _, r)) = T.get_type t1' in
      let phi = T.merge_effects (T.effects_of [T.EWrite(r)]) (T.merge_effects phi1 phi2) in
      T.Assign(t1', t2'), lift_type mty, g2, c2, phi
    |S.Deref(t1), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      T.Deref(t1'), lift_type mty, g1, c1, phi1
    |S.Newrgn, S.THnd(r) ->
      T.Newrgn, T.THnd(r), T.gamma_add r g, T.add_cap r T.Linear c, T.empty_effects
    |S.Aliasrgn(t1, t2), _ -> begin
      let t1', g1, c1, phi1 = check_term env g c t1 in
  (*    print_cap c "c";
      print_cap c1 "c1";*)
      match T.get_type t1' with
      |T.THnd(r) ->
        if T.cap r c1 then
          let t2', g2, c2, phi2 = check_term env g (T.add_cap r T.Relaxed c1) t2 in
          T.Aliasrgn(t1', t2'), lift_type mty, g2, T.add_cap r T.Linear c2, T.merge_effects phi1 phi2
        else
          raise (T.Error (Printf.sprintf "capability of %s not in c1" r))
      |_ -> assert false
    end
    |S.Freergn(t1), S.TUnit -> begin
        let t1', g1, c1, phi1 = check_term env g c t1 in
        match T.get_type t1' with
        |T.THnd(r) when not (T.cap_relaxed r c1) ->
          T.Freergn(t1'), T.TUnit, T.gamma_remove r g1, T.remove_cap r c1, phi1
        |_ -> assert false
    end
    |S.Sequence(t1, t2), _ ->
      let t1', g1, c1, phi1 = check_term env g c t1 in
      let t2', g2, c2, phi2 = check_term env g1 c1 t2 in
      T.Sequence(t1', t2'), lift_type mty, g2, c2, T.merge_effects phi1 phi2
    |_ ->
      Printf.printf "%s\n" (S.show_typed_term t);
      assert false
  in
  T.mk_term te' (merge_mty mty mty') a_l r_l, g_out, c_out, phi_out

let process t =
  let t', _, _, _ = check_term StrMap.empty T.empty_gamma T.empty_capabilities t in
  t'
