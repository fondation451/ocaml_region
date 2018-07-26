(* PARSER for Maxima output *)

%{

  open Parsing
  open Lit

  exception Empty_expression

  let loc() = symbol_start_pos(), symbol_end_pos()

  let aggegate_fun operand operator =
    match operand with
    | [] -> raise Empty_expression
    | init::operand ->
      let rec loop out operand =
        match operand with
        | [] -> out
        | ope::operand' -> loop (operator out ope) operand'
      in loop init operand

%}

%token DUMMY COMA SEMICOLON COLON EQUAL LPAR RPAR LSBRA RSBRA EOF MINUS ADD TIMES DIV POW
%token <int> INTEGER
%token <string> IDENT

%left PLUS MINUS
%left TIMES DIV

%start entry
%type <Lit.t list> entry


%%

entry:
  t = term EOF { t }
;

term:
  | LSBRA e_l = separated_list(COMA, eq) RSBRA { e_l }
  | l = literal_add { [l] }

eq:
  | x = IDENT EQUAL res = literal_add { res }

literal_const:
  | v = IDENT { var v }
  | i = INTEGER { lit i }
  | LPAR l = literal_add RPAR { l }

literal_minus:
  | l = literal_const { l }
  | MINUS l = literal_const
    {
      match l with
      | Lit i -> Lit ((-1) * i)
      | _ -> mul (lit (-1)) l
    }

literal_div:
  | l_l = separated_nonempty_list(DIV, literal_minus)
    { aggegate_fun l_l div }

literal_mul:
  | l_l = separated_nonempty_list(TIMES, literal_div)
    { aggegate_fun l_l mul }

literal_sub:
  | l_l = separated_nonempty_list(MINUS, literal_mul)
    { aggegate_fun l_l sub }

literal_add:
  | l_l = separated_nonempty_list(ADD, literal_sub)
    { aggegate_fun l_l add }
