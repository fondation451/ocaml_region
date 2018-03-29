(* PARSER for OCaml with regions *)

%{

  open Parsing
  open Util
  open Ast

  let loc() = symbol_start_pos(), symbol_end_pos()

%}


%token FUN IF THEN ELSE LET IN REC FST SND NIL CONS REF NEWRGN ALIASRGN FREERGN
%token TRUE FALSE COMA AT ARROW EQUAL LPAR RPAR AFFECT DEREF UNIT HD TL
%token PLUS MINUS TIMES DIV MOD NOT AND OR
%token LT GT LE GE NOT_EQUAL
%token EOF
%token <int> INTEGER
%token <string> IDENT

%left struct_prec
%left INTEGER IDENT TRUE FALSE
%left FST SND HD TL
%left AFFECT
%left OR
%left AND
%left EQUAL NOT_EQUAL
%left LT GT LE GE
%left PLUS MINUS
%left TIMES DIV MOD
%left NOT
%left DEREF
%left FUN

%nonassoc uminus
%nonassoc ELSE

%start entry
%type <Ast.term> entry


%%

entry:
  t = any_term EOF { t }
;

atomic_term:
  |LPAR t = any_term RPAR { t }
  |i = INTEGER { Int(i) }
  |id = IDENT { Var(id) }
  |UNIT { Unit }
  |TRUE { Bool(true) }
  |FALSE { Bool(false) }
  |LPAR t1 = atomic_term COMA t2 = atomic_term RPAR AT t_rgn = atomic_term { Pair(t1, t2, t_rgn) }
  |NIL AT t_rgn = atomic_term { Nil(t_rgn) }
  |CONS t1 = atomic_term t2 = atomic_term AT t_rgn = atomic_term { Cons(t1, t2, t_rgn) }
  |DEREF t = atomic_term { Deref(t) }
;

application_term:
  |t = atomic_term { t }
  |t1 = application_term t2 = application_term
    {
      match t2 with
      |App(t21, t2_l) -> App(t1, t21::t2_l)
      |_ -> App(t1, [t2])
    }
  |t_left = application_term AFFECT t_right = application_term { Assign(t_left, t_right) }
  |REF t = application_term AT t_rgn = application_term { Ref(t, t_rgn) }
  |FST t = application_term { Fst(t) }
  |SND t = application_term { Snd(t) }
  |HD t = application_term { Hd(t) }
  |TL t = application_term { Tl(t) }
  |NEWRGN UNIT { Newrgn }
  |ALIASRGN t_rgn = application_term AT t = application_term { Aliasrgn(t_rgn, t) }
  |FREERGN t_rgn = application_term { Freergn(t_rgn) }
;

%inline op_term:
  |t = application_term { t }
  |t1 = application_term operator = binop t2 = application_term { Binop(operator, t1, t2) }
  |t1 = application_term comp_operator = comp_op t2 = application_term { Comp(comp_operator, t1, t2) }
  |MINUS t = application_term %prec uminus { Neg(t) }
  |NOT t = application_term { Not(t) }
;

statement_term:
  |t = op_term { t }
  |IF t_cond = statement_term THEN t_then = statement_term ELSE t_else = statement_term %prec struct_prec
    { If(t_cond, t_then, t_else) }
;

any_term:
  |t = statement_term { t }
  |FUN id_l = nonempty_list(IDENT) ARROW t_body = any_term AT t_rgn = any_term { Fun(id_l, t_body, t_rgn) }
  |LET id = IDENT EQUAL t1 = any_term IN t2 = any_term { Let(id, t1, t2) }
  |LET REC id_f = IDENT id_l = nonempty_list(IDENT) EQUAL t1 = any_term AT t_rgn = any_term IN t2 = any_term
    { Letrec(id_f, Fun(id_l, t1, t_rgn), t2) }
;

%inline binop:
  |PLUS { Op_add }
  |MINUS { Op_sub }
  |TIMES { Op_mul }
  |DIV { Op_div }
  |MOD { Op_mod }
  |AND { Op_and }
  |OR { Op_or }
;

%inline comp_op:
  |EQUAL { Ceq }
  |NOT_EQUAL { Cneq }
  |LT { Clt }
  |GT { Cgt }
  |LE { Cle }
  |GE { Cge }
;
