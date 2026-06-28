parser grammar KeYCommonParser;
options { tokenVocab = KeYLexer; }

simple_ident
   : id = IDENT
   ;

simple_ident_comma_list
   : id = simple_ident (COMMA id = simple_ident)*
   ;

simple_ident_dots_comma_list_with_docs
:
    simple_ident_dots_with_docs (COMMA simple_ident_dots_with_docs)*
;

simple_ident_dots_with_docs: DOC_COMMENT? simple_ident_dots;

simple_ident_comma_list_with_docs
:
    id+=simple_ident_with_doc (COMMA id+=simple_ident_with_doc)*
;

simple_ident_with_doc: DOC_COMMENT? simple_ident;

sortId
:
    id=simple_ident_dots formal_sort_args? (EMPTYBRACKETS)*
;

formal_sort_args
:
    OPENTYPEPARAMS
    sortId (COMMA sortId)*
    CLOSETYPEPARAMS
;

simple_ident_dots
   : simple_ident (DOT simple_ident)*
   ;

simple_ident_dots_comma_list
   : simple_ident_dots (COMMA simple_ident_dots)*
   ;

funcpred_name
   : (simple_ident_dots DOUBLECOLON)? (name = simple_ident_dots | num = INT_LITERAL)
   ;

varId
   : id = IDENT
   ;

varIds
   : ids = simple_ident_comma_list
   ;

id_declaration
   : id = IDENT (COLON s = sortId)?
   ;
   //this rule produces a String
   
string_value
   : STRING_LITERAL
   ;

