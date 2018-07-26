(* LEXER for Maxima Output *)

{

  open Lexing
  open Parser_maxima

  exception Error of string

  let kwds =
    let h = Hashtbl.create 17 in
    let () = List.iter (fun (s,k) -> Hashtbl.add h s k) [
      "____dummy____", DUMMY;
    ] in
    h

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- {pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum}

}

let regCar = [' '-'!'] | ['#'-'['] | [']'-'~' ]
let escCar = '\\' (['n' 't' '"' '\\'] as esc)
let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = alpha (alpha | '_' | digit | ''')*

rule token = parse
  |'\n' { newline lexbuf; token lexbuf }
  |[' ' '\t' '\r']+ { token lexbuf}
  |'0' | ['1'-'9'] digit* as num
    {
      let i = try int_of_string num with _ -> raise (Error "int overflow") in
      if i > (1 lsl 31)-1 || i < -(1 lsl 31) then
        raise (Error "int overflow")
      else
        INTEGER(i)
    }
  |ident as str_id {try Hashtbl.find kwds str_id with Not_found -> IDENT(str_id)}
  |'+' { ADD }
  |'-' { MINUS }
  |'*' { TIMES }
  |'/' { DIV }
  |'^' { TIMES }
  |',' { COMA }
  |';' { SEMICOLON }
  |':' { COLON }
  |'=' { EQUAL }
  |'(' { LPAR }
  |')' { RPAR }
  |'[' { LSBRA }
  |']' { RSBRA }
  |eof {EOF}
  |_ { raise (Error (lexeme lexbuf)) }
