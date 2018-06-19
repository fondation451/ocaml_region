(* Main *)

open Printf
open Lexing
open Util

let parse_only = ref false
let verbose = ref false

let input_file = ref ""
let output_file = ref ""

let usage = "usage: rcaml [options] file.ml"

let report_loc (b, e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  eprintf "Line %d, characters %d-%d:\n" l fc lc

let set_file f s = f := s

let options = [
  "-v", Arg.Set verbose, "  Verbose mode"
]

let () =
  Arg.parse options (set_file input_file) usage;

  if not (Filename.check_suffix !input_file ".mlc") then begin
    eprintf "The input file must be a .mlc\n@?";
    Arg.usage options usage;
    exit 1
  end;

  let f = open_in !input_file in
  let buf = Lexing.from_channel f in

  try

    let prog = Parser.entry Lexer.token buf in
    Printf.printf "(********** RCAML **********)\n%s\n\n" (Ast.show_typed_term prog);

    let prog = Ast_to_type.process prog in
    Printf.printf "(********** RCAML TYPED **********)\n%s\n\n" (Ast.show_typed_term prog);

    let prog = Type_to_ls.process prog in
    Printf.printf "(********** RCAML LS **********)\n%s\n\n" (Ast.show_typed_term prog);

    let prog = Ls_to_simpl.process prog in
    Printf.printf "(********** RCAML SIMPL **********)\n%s\n\n" (Simpl.show_typed_term prog);

    let prog = Simpl_to_check.process prog in
    Printf.printf "(********** RCAML CHECKED **********)\n%s\n\n" (Check.show_typed_term prog);

    let bound = Check_to_analysis.process prog in
    Printf.printf "(********** RCAML REGIONS BYTES BOUND **********)\n";
    Printf.printf "Bound: %d bytes\n" bound;

    ()

  with
  |Lexer.Error(str) ->
    report_loc (lexeme_start_p buf, lexeme_end_p buf);
    eprintf "Lexing error : %s\n@." str;
    exit 1
  |Parser.Error ->
    report_loc (lexeme_start_p buf, lexeme_end_p buf);
    eprintf "Syntax error\n@.";
    exit 1
  |Ast.Type_Error(str) ->
    eprintf "Typing error : %s\n@." str;
    exit 1
  |Ast.Ls_Error(str) ->
    eprintf "Ls error : %s\n@." str;
    exit 1
  |Simpl.Error(str) ->
    eprintf "Simpl error : %s\n@." str;
    exit 1
  |Check.Error(str) ->
    eprintf "Check error : %s\n@." str;
    exit 1
 (* |_ ->
    eprintf "Compilation error\n@."; *)
