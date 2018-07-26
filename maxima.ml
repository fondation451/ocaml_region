(* Maxima command generation *)

open Util
open Lit
open Lexing

let to_maxima l =
  let out = Buffer.create 5 in
  let rec loop l out =
    match l with
    | Var v -> v::out
    | Lit i -> (string_of_int i)::out
    | Add (l1, l2) -> "("::(loop l1 (") + ("::(loop l2 (")"::out))))
    | Mul (l1, l2) -> "("::(loop l1 (") * ("::(loop l2 (")"::out))))
    | Div (l1, l2) -> "("::(loop l1 (") / ("::(loop l2 (")"::out))))
  in
  List.iter (Buffer.add_string out) (loop l []);
  Buffer.contents out

let max_solve l c =
  let eq = to_maxima l in
  "solve(" ^ eq ^ "," ^ c ^ ")"

let max_canonic l =
  let eq = to_maxima l in
  "expand(" ^ eq ^ ")"

let mk_maxima_cmd cmd = "maxima --very-quiet -qr \"display2d:false$ " ^ cmd ^ ";\""

let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)

let execute cmd =
  let max_cmd = mk_maxima_cmd cmd in
  let out = syscall max_cmd in
(*  Printf.printf "%s\n%s\n" max_cmd out; print_newline ();*)
  out

let to_lit s =
  let buf = Lexing.from_string s in
  Parser_maxima.entry Lexer_maxima.token buf

let min_sol l_l = List.hd l_l(*list_min (fun l l' -> compare (cost_of l) (cost_of l')) l_l*)

let canonic l =
  let cmd = max_canonic l in
  let out = execute cmd in
  let out' = to_lit out in
  Printf.printf "%s\n%s\n%s\n" cmd out (list_str out' Lit.show); print_newline ();
  min_sol out'


let solve l c =
  let cmd = max_solve l c in
  let out = execute cmd in
  Printf.printf "%s\n%s\n" cmd out; print_newline ();
  min_sol (to_lit out)
