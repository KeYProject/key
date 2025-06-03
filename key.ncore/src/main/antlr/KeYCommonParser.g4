parser grammar KeYCommonParser;


options { tokenVocab = KeYLexer; }
simple_ident
   : id = IDENT
   ;

simple_ident_comma_list
   : id = simple_ident (COMMA id = simple_ident)*
   ;

sortId
   : id = simple_ident_dots (EMPTYBRACKETS)*
   ;

simple_ident_dots
   : simple_ident (DOT simple_ident)*
   ;

simple_ident_dots_comma_list
   : simple_ident_dots (COMMA simple_ident_dots)*
   ;

funcpred_name
   : (sortId DOUBLECOLON)? (name = simple_ident_dots | num = INT_LITERAL)
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

