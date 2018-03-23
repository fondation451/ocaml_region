(* PARSER for OCaml with regions *)

%{

  open Parsing
  open Rcaml_ast

  let loc() = symbol_start_pos(), symbol_end_pos()

%}


%token FUN IF THEN ELSE LET IN REC FST SND NIL CONS REF NEWRGN ALIASRGN FREERGN
%token TRUE FALSE COMA AT ARROW EQUAL LPAR RPAR AFFECT DEREF UNIT
%token PLUS MINUS TIMES DIV MOD NOT AND OR
%token LT GT LE GE NOT_EQUAL
%token EOF
%token <int> INTEGER
%token <string> IDENT

%left struct_prec
%left INTEGER IDENT TRUE FALSE
%left FST SND
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
%type <Rcaml_ast.term> entry


%%

entry:
  t = term EOF { t }
;

term:
  |FUN id = IDENT ARROW t_body = term AT t_rgn = term { TFun(id, t_body, t_rgn) }
  |t1 = term t2 = term { TApp(t1, t2) }
  |IF t_cond = term THEN t_then = term ELSE t_else = term %prec struct_prec { TIf(t_cond, t_then, t_else) }
  |LET id = IDENT EQUAL t1 = term IN t2 = term { TLet(id, t1, t2) }
  |LET REC id_f = IDENT id_x = IDENT EQUAL t1 = term AT t_rgn = term IN t2 = term { TLetrec(id_f, id_x, t1, t_rgn, t2) }
  |LPAR t1 = term COMA t2 = term RPAR AT t_rgn = term { TPair(t1, t2, t_rgn) }
  |FST t = term { TFst(t) }
  |SND t = term { TSnd(t) }
  |NIL AT t_rgn = term { TNil(t_rgn) }
  |CONS t1 = term t2 = term AT t_rgn = term { TCons(t1, t2, t_rgn) }
  |REF t = term AT t_rgn = term { TRef(t, t_rgn) }
  |t_left = term AFFECT t_right = term { TAssign(t_left, t_right) }
  |DEREF t = term { TDeref(t) }
  |NEWRGN LPAR RPAR { TNewrgn }
  |ALIASRGN t_rgn = term AT t = term { TAliasrgn(t_rgn, t) }
  |FREERGN t_rgn = term { TFreergn(t_rgn) }
  |t1 = term operator = binop t2 = term { TBinop(operator, t1, t2) }
  |t1 = term comp_operator = comp_op t2 = term { TComp(comp_operator, t1, t2) }
  |MINUS t = term %prec uminus { TNeg(t) }
  |NOT t = term { TNot(t) }
  |UNIT { TUnit }
  |TRUE { TBool(true) }
  |FALSE { TBool(false) }
  |i = INTEGER { TInt(i) }
  |id = IDENT { TVar(id) }
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
