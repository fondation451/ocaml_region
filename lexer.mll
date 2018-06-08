(* LEXER for OCaml with regions *)

{

  open Lexing
  open Util
  open Parser

  exception Error of string

  let kwds =
    let h = Hashtbl.create 17 in
    let () = List.iter (fun (s,k) -> Hashtbl.add h s k) [
      "fun", FUN;
      "if", IF;
      "then", THEN;
      "else", ELSE;
      "let", LET;
      "in", IN;
      "rec", REC;
      "fst", FST;
      "snd", SND;
      "hd", HD;
      "tl", TL;
      "Nil", NIL;
      "Cons", CONS;
      "ref", REF;
      "newrgn", NEWRGN;
      "aliasrgn", ALIASRGN;
      "freergn", FREERGN;
      "mod", MOD;
      "not", NOT;
      "begin", BEGIN;
      "end", END;
      "match", MATCH;
      "with", WITH;
      "size", SIZE;
      "rpair", RPAIR;
      "rcons", RCONS;
      "rref", RREF;
      "rhnd", RHND;
      "_length", LENGTH;
      "Leaf", LEAF;
      "Node", NODE;
      "_node", NODEP;
      "_depth", DEPTH;
    ] in
    h

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- {pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum}

  let reg_of_esc = function
      | '\\' -> '\\'
      | 'n' -> '\n'
      | 't' -> '\t'
      | '"' -> '"'
      | _ -> failwith "reg_of_esc"

}

let regCar = [' '-'!'] | ['#'-'['] | [']'-'~' ]
let escCar = '\\' (['n' 't' '"' '\\'] as esc)
let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = alpha (alpha | '_' | digit)*
let ident_cont = '_' alpha (alpha | '_' | digit)*

rule token = parse
  |'\n' { newline lexbuf; token lexbuf }
  |[' ' '\t' '\r']+ { token lexbuf}
  |"true" { TRUE }
  |"false" { FALSE }
  |'0' | ['1'-'9'] digit* as num
    {
      let i =
      try int_of_string num
      with _ -> raise (Error "int overflow") in
      if i > (1 lsl 31)-1 || i < -(1 lsl 31)
      then raise (Error "int overflow")
      else INTEGER(i)
    }
  |ident as str_id {try Hashtbl.find kwds str_id with Not_found -> IDENT(str_id)}
  |ident_cont as str_id
    {
      try Hashtbl.find kwds str_id with Not_found -> raise (Error "")
    }
  |',' { COMA }
  |';' { SEMICOLON }
  |':' { COLON }
  |'@' { AT }
  |"|" { CASE }
  |"->" { ARROW }
  |'=' { EQUAL }
  |"<>" { NOT_EQUAL }
  |'<' { LT }
  |'>' { GT }
  |"<=" { LE }
  |">=" { GE }
  |"()" { UNIT }
  |'(' { LPAR }
  |')' { RPAR }
  |'[' { LSBRA }
  |']' { RSBRA }
  |":=" { AFFECT }
  |'!' { DEREF }
  |'+' { PLUS }
  |'-' { MINUS }
  |'*' { TIMES }
  |'/' { DIV }
  |"&&" { AND }
  |"||" { OR }
  |'{' { LBRA }
  |'}' { RBRA }
  |"(*" {comment_block lexbuf}
  |eof {EOF}
  |_
    { raise (Error (lexeme lexbuf)) }

and comment_block = parse
  |"*)" { token lexbuf }
  |'\n' { newline lexbuf; comment_block lexbuf }
  |_ { comment_block lexbuf }
  |eof { raise (Error("Unfinished comment !\n")) }
