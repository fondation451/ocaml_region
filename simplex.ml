(* OCPLIB SIMPLEX interface *)

(* Module parametrisation *)

module Var = struct
  type t = string
  let print fmt s = Format.fprintf fmt "%s" s
  let compare = String.compare
  let is_int _ = true
end

module Ex = struct
  module S = Set.Make(String)
  include S
  let print fmt s = match elements s with
    | [] -> Format.fprintf fmt "()"
    | e::l ->
      Format.fprintf fmt "%s" e;
      List.iter (Format.fprintf fmt ", %s") l
end

module Rat = struct
  open Num
  type t = num
  let add = ( +/ )
  let mult = ( */ )
  let compare = compare_num
  let equal = ( =/ )
  let zero = Int 0
  let one = Int 1
  let m_one = Int (-1)
  let is_zero n = n =/ zero
  let to_string = string_of_num

  let print fmt t = Format.fprintf fmt "%s" (to_string t)
  let is_int = is_integer_num
  let div = (//)
  let sub = (-/)
  let is_one v = v =/ Int 1
  let is_m_one v = v =/ Int (-1)
  let sign = sign_num
  let min = min_num
  let abs = abs_num
  let minus = minus_num
end

module Sim = OcplibSimplex.Basic.Make(Var)(Rat)(Ex)

(* **** *)

(* My interface *)

let line_name = let cpt = ref (-1) in fun () -> incr cpt; "line"^(string_of_int !cpt)

let str_of_line l bound = ""

let create () = Sim.Core.empty ~is_int:true ~check_invs:true ~debug:0

let mk_const i = Some(Num.Int(i), Rat.zero)

let add_var sim v =
  let out, _ = Sim.Assert.var sim v (mk_const 0) (Ex.singleton (Printf.sprintf "%s>=0" v)) None Ex.empty in
  out

let mk_line l = Sim.Core.P.from_list l

let add_line sim l bound =
  let line = mk_line l in
  let out, _ = Sim.Assert.poly sim line (line_name ()) None Ex.empty bound (Ex.singleton (str_of_line l bound)) in
  out

let compute sim l =
  let line = mk_line l in
  let sim, opt = Sim.Solve.maximize sim line in
  Format.printf "The problem 'max %a' ...@." Sim.Core.P.print line;
(*  begin*)
    match Sim.Result.get opt sim with
    |Sim.Core.Unknown     -> assert false
    |Sim.Core.Sat _       -> assert false
    |Sim.Core.Unsat ex    -> raise (No_side_effect.No_Side_Effect_Error "Unsat memory problem")
    |Sim.Core.Unbounded _ -> raise (No_side_effect.No_Side_Effect_Error "Unbounded memory") (* Format.printf " is unbounded@." *)
    |Sim.Core.Max (mx,_)  -> 
      let {Sim.Core.max_v; is_le; reason} = Lazy.force mx in
      max_v
(*      let {Sim.Core.max_v; is_le; reason} = Lazy.force mx in
      Format.printf " has an upper bound: %a (is_le = %b)(reason: %a)@." Rat.print max_v is_le Ex.print reason;
  end;
  Format.printf "@."*)

let () =
  let sim = create () in

  let sim = add_var sim "x" in
  let sim = add_var sim "y" in

  let l1 = ["x", Rat.one; "y", Rat.one] in
  let l2 = ["y", Rat.one] in
  let l3 = ["y", Rat.m_one] in

  let sim = add_line sim l1 (mk_const 1) in
(*  let sim = Sim.Solve.solve sim in *)

  compute sim l1;
  compute sim l2;
  compute sim l3;
  ()
