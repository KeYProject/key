parser grammar KeYGlobalDeclParser;

import KeYTacletParser;

decls
   : (string = programSource // for problems
   | one_include_statement | options_choice | option_decls | sort_decls | prog_var_decls | schema_var_decls | pred_decls | func_decls | transform_decls | datatype_decls | ruleset_decls
   | rulesOrAxioms // for problems
   )*
   ;

one_include_statement
   : (INCLUDE | INCLUDELDTS) one_include (COMMA one_include)* SEMI
   ;

one_include
   : absfile = IDENT
   | relfile = string_value
   ;

options_choice
   : WITHOPTIONS activated_choice (COMMA activated_choice)* SEMI
   ;

activated_choice
   : cat = IDENT COLON choice_ = IDENT
   ;

rulesOrAxioms
   : doc = DOC_COMMENT? (RULES | AXIOMS) (choices = option_list)? (LBRACE (s = taclet SEMI?)* RBRACE)
   ;

programSource
   : PROGRAMSOURCE result = oneProgramSource SEMI
   ;

oneProgramSource
   : (string_value | COLON)+
   ;

schema_var_decls
   : SCHEMAVARIABLES LBRACE (one_schema_var_decl SEMI)* RBRACE
   ;

formal_sort_param_decls
: OPENTYPEPARAMS
      formal_sort_param_decl (COMMA formal_sort_param_decl)*
      CLOSETYPEPARAMS
;

formal_sort_param_decl
:
    (PLUS | MINUS)? simple_ident
;

pred_decl
   : doc = DOC_COMMENT? pred_name = funcpred_name formal_sort_param_decls? (whereToBind = where_to_bind)? argSorts = arg_sorts SEMI
   ;

pred_decls
   : PREDICATES LBRACE (pred_decl)* RBRACE
   ;

func_decl
   : doc = DOC_COMMENT? (UNIQUE)? retSort = sortId func_name = funcpred_name formal_sort_param_decls? whereToBind = where_to_bind? argSorts = arg_sorts SEMI
   ;

/**
\datatypes {
 \free List = Nil | Cons(any head, List tail);
}
*/
datatype_decls
	 : DATATYPES LBRACE datatype_decl* RBRACE
   ;

datatype_decl
   : doc = DOC_COMMENT?
   // weigl: all datatypes are free!
   // FREE?
   name = simple_ident formal_sort_param_decls? EQUALS datatype_constructor (OR datatype_constructor)* SEMI
   ;

datatype_constructor
   :
      doc=DOC_COMMENT?
      name = simple_ident (LPAREN (argSort += sortId argName += simple_ident (COMMA argSort += sortId argName += simple_ident)*)? RPAREN)?
   ;

func_decls
   : FUNCTIONS LBRACE (func_decl)* RBRACE
   ;

prog_var_decls
   : PROGRAMVARIABLES LBRACE (kjt = typemapping var_names = simple_ident_comma_list_with_docs SEMI)* RBRACE
   ;

typemapping
   : type = simple_ident_dots (EMPTYBRACKETS)*
   ;

option_decls
   : OPTIONSDECL LBRACE (choice SEMI)* RBRACE
   ;

choice
   : maindoc += DOC_COMMENT* category = IDENT (COLON LBRACE optionDecl (COMMA optionDecl)* RBRACE)?
   ;

optionDecl
   : doc += DOC_COMMENT? choice_option += IDENT
   ;

sort_decls
   : SORTS LBRACE (one_sort_decl)* RBRACE
   ;

one_sort_decl
:
  doc=DOC_COMMENT?
  (
     GENERIC  sortIds=simple_ident_dots_comma_list_with_docs
        (ONEOF sortOneOf = oneof_sorts)?
        (EXTENDS sortExt = extends_sorts)? SEMI
    | PROXY  sortIds=simple_ident_dots_comma_list_with_docs (EXTENDS sortExt=extends_sorts)? SEMI
    | ABSTRACT? (sortIds=simple_ident_dots_comma_list_with_docs | parametric_sort_decl) (EXTENDS sortExt=extends_sorts)?  SEMI
    | ALIAS simple_ident_dots EQUALS sortId SEMI
  )
;

parametric_sort_decl
:
		DOC_COMMENT?
    simple_ident_dots
    formal_sort_param_decls
;

extends_sorts
   : sortId (COMMA sortId)*
   ;

oneof_sorts
   : LBRACE s = sortId (COMMA s = sortId)* RBRACE
   ;

arg_sorts
   : (LPAREN sortId (COMMA sortId)* RPAREN)?
   ;

where_to_bind
   : LBRACE b += (TRUE | FALSE) (COMMA b += (TRUE | FALSE))* RBRACE
   ;

ruleset_decls
   : HEURISTICSDECL LBRACE (id += simple_ident_with_doc SEMI)* RBRACE
   ;

transform_decl
   : doc = DOC_COMMENT? (retSort = sortId | FORMULA) trans_name = funcpred_name argSorts = arg_sorts_or_formula SEMI
   ;

transform_decls
   : TRANSFORMERS LBRACE (transform_decl)* RBRACE
   ;
   // like arg_sorts but admits also the keyword "\formula"
   
arg_sorts_or_formula
   : (LPAREN arg_sorts_or_formula_helper (COMMA arg_sorts_or_formula_helper)* RPAREN)?
   ;

arg_sorts_or_formula_helper
   : sortId
   | FORMULA
   ;

