(* PARSER for OCaml with regions *)

%{

  open Parsing
  open Ast
  open Util

  let loc() = symbol_start_pos(), symbol_end_pos()

  let mk te = Ast.mk_term te Ast.TUnit [] []

%}


%token FUN IF THEN ELSE LET IN REC FST SND NIL CONS REF NEWRGN ALIASRGN FREERGN BEGIN END
%token TRUE FALSE COMA SEMICOLON AT ARROW EQUAL LPAR RPAR AFFECT DEREF UNIT HD TL LBRA RBRA LSBRA RSBRA
%token PLUS MINUS TIMES DIV MOD NOT AND OR
%token MATCH WITH CASE
%token SIZE COLON
%token LT GT LE GE NOT_EQUAL
%token RPAIR RCONS RREF RHND LENGTH
%token LEAF NODE NODEP DEPTH
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
%type <Ast.typed_term> entry


%%

entry:
  t = any_term EOF { t }
;

atomic_term:
  |BEGIN t = sequence_term END { t }
  |LPAR t = sequence_term RPAR { t }
  |i = INTEGER { mk (Int i) }
  |id = IDENT { mk (Var id) }
  |UNIT { mk Unit }
  |TRUE { mk (Bool true) }
  |FALSE { mk (Bool false) }
  |NIL { mk Nil }
  |LEAF { mk Leaf }
  |CONS t1 = atomic_term t2 = atomic_term AT t_rgn = atomic_term { mk (Cons (t1, t2, t_rgn)) }
  |NODE t1 = atomic_term t2 = atomic_term t3 = atomic_term AT t_rgn = atomic_term
    { mk (Node (t1, t2, t3, t_rgn)) }
  |DEREF t = atomic_term { mk (Deref t) }
;

application_term:
  |t = atomic_term { t }
  |t1 = atomic_term t_l = nonempty_list(atomic_term)
    {
      let v_l =
        List.map
          (fun t ->
            match get_term t with
            | Var x -> x
            | _ -> mk_var ())
          t_l
      in
      List.fold_left2
        (fun out v t2 ->
          match get_term t2 with
          | Var _ -> out
          | _ -> mk (Let (v, t2, out)))
        (mk (App (t1, v_l))) v_l t_l
    }
  |t_left = application_term AFFECT t_right = application_term { mk (Assign (t_left, t_right)) }
  |REF t = application_term AT t_rgn = application_term { mk (Ref (t, t_rgn)) }
  |FST t = application_term { mk (Fst t) }
  |SND t = application_term { mk (Snd t) }
  |HD t = application_term { mk (Hd t) }
  |TL t = application_term { mk (Tl t) }
  |NEWRGN UNIT { mk Newrgn }
  |ALIASRGN t_rgn = application_term IN t = any_term { mk (Aliasrgn (t_rgn, t)) }
  |FREERGN t_rgn = application_term { mk (Freergn t_rgn) }
  |LPAR t1 = application_term COMA t2 = application_term RPAR AT t_rgn = application_term { mk (Pair (t1, t2, t_rgn)) }
  |LSBRA elem_l = separated_list(SEMICOLON, application_term) RSBRA AT t_rgn = application_term
    {
      let rec loop elem_l =
        match elem_l with
        |[] -> mk Nil
        |hd::tl -> mk (Cons (hd, loop tl, t_rgn))
      in loop elem_l
    }
;

%inline op_term:
  |t = application_term { t }
  |t1 = application_term operator = binop t2 = application_term { mk (Binop (operator, t1, t2)) }
  |t1 = application_term comp_operator = comp_op t2 = application_term { mk (Comp(comp_operator, t1, t2)) }
  |MINUS t = application_term %prec uminus { mk (Neg t) }
  |NOT t = application_term { mk (Not t) }
;

statement_term:
  |t = op_term { t }
  |IF t_cond = statement_term THEN t_then = statement_term ELSE t_else = statement_term %prec struct_prec
    { mk (If (t_cond, t_then, t_else)) }
  |MATCH t_match = statement_term WITH
   CASE NIL ARROW t_nil = statement_term
   CASE CONS id_x = IDENT id_xs = IDENT ARROW t_cons = statement_term
    {
      match get_term t_match with
      | Var v -> mk (MatchList (v, t_nil, id_x, id_xs, t_cons))
      | _ ->
        let v = mk_var () in
        mk (Let (v, t_match, mk (MatchList (v, t_nil, id_x, id_xs, t_cons))))
    }
  |MATCH t_match = statement_term WITH
   CASE LEAF ARROW t_leaf = statement_term
   CASE NODE id_x = IDENT id_l = IDENT id_r = IDENT ARROW t_node = statement_term
    {
      match get_term t_match with
      | Var v -> mk (MatchTree (v, t_leaf, id_x, id_l, id_r, t_node))
      | _ ->
        let v = mk_var () in
        mk (Let (v, t_match, mk (MatchTree (v, t_leaf, id_x, id_l, id_r, t_node))))
    }
;

pot_term:
  |RPAIR { PLit(Util.cost_of Util.RPAIR) }
  |RCONS { PLit(Util.cost_of Util.RCONS) }
  |RREF { PLit(Util.cost_of Util.RREF) }
  |RHND { PLit(Util.cost_of Util.RHND) }
  |SIZE LPAR v = IDENT RPAR { PSize(v) }
  |LENGTH LPAR v = IDENT RPAR { PLen(v) }
  |NODEP LPAR v = IDENT RPAR { PNode(v) }
  |DEPTH LPAR v = IDENT RPAR { PDepth(v) }
  |i = INTEGER { PLit(i) }
  |p1 = pot_term PLUS p2 = pot_term { PAdd(p1, p2) }
  |p1 = pot_term TIMES p2 = pot_term { PMul(p1, p2) }
  |MINUS p1 = pot_term { PMin(p1) }
  |LPAR p1 = pot_term RPAR { p1 }
;

rgn_pot_term:
  |v = IDENT COLON p1 = pot_term ARROW p2 = pot_term { (v, (p1, p2)) }
;

any_term:
  |t = statement_term { t }
  |FUN id_l = nonempty_list(IDENT) ARROW t_body = any_term AT t_rgn = any_term { mk (Fun ("", id_l, t_body, t_rgn, None)) }
  |LET id = IDENT EQUAL t1 = any_term IN t2 = any_term { mk (Let (id, t1, t2)) }
  |LET REC id_f = IDENT id_l = nonempty_list(IDENT) EQUAL t1 = any_term AT t_rgn = any_term IN t2 = any_term
    { mk (Letrec (id_f, mk (Fun (id_f, id_l, t1, t_rgn, None)), t2)) }
  |LET REC id_f = IDENT id_l = nonempty_list(IDENT) EQUAL
    LBRA pot = separated_list(SEMICOLON, rgn_pot_term) RBRA
    t1 = any_term AT t_rgn = any_term IN t2 = any_term
    {
      let pot = match pot with |[] -> None |_ -> Some(pot) in
      mk (Letrec (id_f, mk (Fun (id_f, id_l, t1, t_rgn, pot)), t2))
    }
;

sequence_term:
  |t = any_term { t }
  |t1 = sequence_term SEMICOLON t2 = sequence_term { mk (Sequence (t1, t2)) }
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
