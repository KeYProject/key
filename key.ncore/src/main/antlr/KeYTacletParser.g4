parser grammar KeYTacletParser;

import KeYSequentParser;

taclet
   : doc = DOC_COMMENT? (LEMMA)? name = IDENT (choices_ = option_list)? LBRACE (form = term | (SCHEMAVAR one_schema_var_decl SEMI)* (ASSUMES LPAREN assumesSeq = seq RPAREN)? (FIND LPAREN find = termorseq RPAREN (IGNOREUPDATELEVEL | SAMEUPDATELEVEL | INSEQUENTSTATE | ANTECEDENTPOLARITY | SUCCEDENTPOLARITY)*)? (VARCOND LPAREN varexplist RPAREN)* goalspecs modifiers) RBRACE
   ;

option_list
   : LPAREN (option_expr (COMMA option_expr)*) RPAREN
   ;

option
   : cat = IDENT COLON value = IDENT
   ;

option_expr
   : option_expr AND option_expr # option_expr_and
   | option_expr OR option_expr # option_expr_or
   | NOT option_expr # option_expr_not
   | LPAREN option_expr RPAREN # option_expr_paren
   | option # option_expr_prop
   ;

goalspec
   : (name = string_value (LBRACKET tag=simple_ident RBRACKET)? COLON)? (rwObj = replacewith addSeq = add? addRList = addrules? addpv = addprogvar? | addSeq = add (addRList = addrules)? | addRList = addrules)
   ;

replacewith
   : REPLACEWITH LPAREN o = termorseq RPAREN
   ;

add
   : ADD LPAREN s = seq RPAREN
   ;

addrules
   : ADDRULES LPAREN lor = tacletlist RPAREN
   ;

addprogvar
   : ADDPROGVARS LPAREN pvs = pvset RPAREN
   ;

tacletlist
   : taclet (COMMA taclet)*
   ;

pvset
   : varId (COMMA varId)*
   ;

rulesets
   : HEURISTICS LPAREN ruleset (COMMA ruleset)* RPAREN
   ;

ruleset
   : id = IDENT
   ;

metaId
   : id = simple_ident
   ;

varexplist
   : varexp (COMMA varexp)*
   ;

varexp
   : negate = NOT_? varexpId (LBRACKET parameter += IDENT (COMMA parameter += IDENT)* RBRACKET)? (LPAREN varexp_argument (COMMA varexp_argument)* RPAREN)?
   ;

varexpId
   : // weigl, 2021-03-12: This will be later just an arbitrary identifier. Only for backwards compatibility.
   APPLY_UPDATE_ON_RIGID
   | DROP_EFFECTLESS_ELEMENTARIES
   | SIMPLIFY_IF_THEN_ELSE_UPDATE
   | DIFFERENT
   | EQUAL_UNIQUE
   | NEW
   | NEW_TYPE_OF
   | HAS_ELEMENTARY_SORT
   | SAME
   | ISSUBTYPE
   | STRICT ISSUBTYPE
   | HASSORT
   ;

varexp_argument
   :
   //weigl: Ambguity between term (which can also contain simple_ident_dots and sortId)
   
   //       suggestion add an explicit keyword to request the sort by name or manually resolve later in builder
   TYPEOF LPAREN y = varId RPAREN
   | term
   ;

goalspecs
   : CLOSEGOAL
   | goalspecwithoption (SEMI goalspecwithoption)*
   ;

goalspecwithoption
   : soc = option_list LBRACE goalspec RBRACE
   | goalspec
   ;

triggers
   : TRIGGER LBRACE id = simple_ident RBRACE t = term (AVOID avoidCond += term (COMMA avoidCond += term)*)? SEMI
   ;

modifiers
   : (rs = rulesets | NONINTERACTIVE | DISPLAYNAME dname = string_value | HELPTEXT htext = string_value | triggers)*
   ;
   //TODO Split
   
one_schema_var_decl
   : MODALOPERATOR one_schema_modal_op_decl
   | PROGRAM (schema_modifiers)? id = simple_ident (LBRACKET nameString = simple_ident EQUALS parameter = simple_ident_dots RBRACKET)? ids = simple_ident_comma_list
   | FORMULA (schema_modifiers)? ids = simple_ident_comma_list
   | UPDATE (schema_modifiers)? ids = simple_ident_comma_list
   | SKOLEMFORMULA (schema_modifiers)? ids = simple_ident_comma_list
   | (TERM | (VARIABLES | VARIABLE) | SKOLEMTERM) (schema_modifiers)? s = sortId ids = simple_ident_comma_list
   ;

schema_modifiers
   : LBRACKET opts = simple_ident_comma_list RBRACKET
   ;

one_schema_modal_op_decl
   : (LPAREN sort = sortId RPAREN)? LBRACE ids = simple_ident_comma_list RBRACE id = simple_ident
   ;

