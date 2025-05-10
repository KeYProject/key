parser grammar KeYTermParser;


options { tokenVocab = KeYLexer; }
import KeYCommonParser;
term
   : parallel_term
   ; // weigl: should normally be equivalence_term
   
   //labeled_term: a=parallel_term (LGUILLEMETS labels=label RGUILLEMETS)?;
   
parallel_term
   : a = elementary_update_term (PARALLEL b = elementary_update_term)*
   ;

elementary_update_term
   : a = equivalence_term (ASSIGN b = equivalence_term)?
   ;

equivalence_term
   : a = implication_term (EQV b += implication_term)*
   ;

implication_term
   : a = disjunction_term (IMP b = implication_term)?
   ;

disjunction_term
   : a = conjunction_term (OR b += conjunction_term)*
   ;

conjunction_term
   : a = term60 (AND b += term60)*
   ;

term60
   : unary_formula
   | equality_term
   ;

unary_formula
   : NOT sub = term60 # negation_term
   | (FORALL | EXISTS) bound_variables sub = term60 # quantifierterm
   | MODALITY sub = term60 # modality_term
   ;

equality_term
   : a = comparison_term ((NOT_EQUALS | EQUALS) b = comparison_term)?
   ;

comparison_term
   : a = weak_arith_term ((LESS | LESSEQUAL | GREATER | GREATEREQUAL | UTF_PRECEDES | UTF_SUBSET_EQ | UTF_SUBSEQ | UTF_IN) b = weak_arith_term)?
   ;

weak_arith_term
   : a = strong_arith_term_1 (op += (PLUS | MINUS | UTF_UNION | UTF_INTERSECT | UTF_SETMINUS) b += strong_arith_term_1)*
   ;

strong_arith_term_1
   : a = strong_arith_term_2 (STAR b += strong_arith_term_2)*
   ;

strong_arith_term_2
   : a = atom_prefix (op += (PERCENT | SLASH) b += atom_prefix)*
   ;

update_term
   : (LBRACE u = parallel_term RBRACE) (atom_prefix | unary_formula)
   ;

substitution_term
   : LBRACE SUBST bv = one_bound_variable SEMI replacement = comparison_term RBRACE (atom_prefix | unary_formula)
   ;

cast_term
   : (LPAREN sort = sortId RPAREN) sub = atom_prefix
   ;

unary_minus_term
   : MINUS sub = atom_prefix
   ;

atom_prefix
   : update_term
   | substitution_term
   | locset_term
   | cast_term
   | unary_minus_term
   | bracket_term
   ;

bracket_term
   : primitive_labeled_term (bracket_suffix_heap)* attribute*
   ;

bracket_suffix_heap
   : brace_suffix (AT heap = bracket_term)?
   ;

brace_suffix
   : LBRACKET target = term ASSIGN val = term RBRACKET # bracket_access_heap_update
   | LBRACKET id = simple_ident args = argument_list RBRACKET # bracket_access_heap_term
   | LBRACKET STAR RBRACKET # bracket_access_star
   | LBRACKET indexTerm = term (DOTRANGE rangeTo = term)? RBRACKET # bracket_access_indexrange
   ;

primitive_labeled_term
   : primitive_term (LGUILLEMETS labels = label RGUILLEMETS)?
   ;

termParen
   : LPAREN term RPAREN (attribute)*
   ;

abbreviation
   : AT name = simple_ident
   ;

primitive_term
   : termParen
   | ifThenElseTerm
   | ifExThenElseTerm
   | abbreviation
   | accessterm
   | literals
   ;

termEOF
   : term EOF
   ; // toplevel
   
boolean_literal
   : TRUE
   | FALSE
   ;

literals
   : boolean_literal
   | char_literal
   | integer
   | floatnum
   | string_literal
   | emptyset
   ;
   //this rule produces a StringLiteral
   
string_literal
   : id = STRING_LITERAL
   ;

emptyset
   : UTF_EMPTY
   ;

bound_variables
   : var = one_bound_variable (COMMA var = one_bound_variable)* SEMI
   ;

one_bound_variable
   : s = sortId? id = simple_ident
   ;

argument_list
   : LPAREN (term (COMMA term)*)? RPAREN
   ;

integer_with_minux
   : MINUS? integer
   ;

integer
   : (INT_LITERAL | HEX_LITERAL | BIN_LITERAL)
   ;

floatnum
   : // called floatnum because "float" collide with the Java language
   (MINUS)? FLOAT_LITERAL # floatLiteral
   | (MINUS)? DOUBLE_LITERAL # doubleLiteral
   | (MINUS)? REAL_LITERAL # realLiteral
   ;

char_literal
   : CHAR_LITERAL
   ;

location_term
   : LPAREN obj = equivalence_term COMMA field = equivalence_term RPAREN
   ;

ifThenElseTerm
   : IF LPAREN condF = term RPAREN THEN LPAREN thenT = term RPAREN ELSE LPAREN elseT = term RPAREN
   ;

ifExThenElseTerm
   : IFEX exVars = bound_variables LPAREN condF = term RPAREN THEN LPAREN thenT = term RPAREN ELSE LPAREN elseT = term RPAREN
   ;

locset_term
   : LBRACE (l = location_term (COMMA l = location_term)*)? RBRACE
   ;

/**
 * Access: a.b.c@f, T.staticQ()
 */ accessterm
   :
   // OLD
   (sortId DOUBLECOLON)? firstName = simple_ident
/*Faster version
  simple_ident_dots
  ( EMPTYBRACKETS*
    DOUBLECOLON
    simple_ident
  )?*/
   
   call? (attribute)*
   ;

attribute
   : DOT STAR # attribute_star
   | DOT id = simple_ident call? (AT heap = bracket_term)? # attribute_simple
   | DOT LPAREN sort = sortId DOUBLECOLON id = simple_ident RPAREN call? (AT heap = bracket_term)? # attribute_complex
   ;

call
   : ((LBRACE boundVars = bound_variables RBRACE)? argument_list)
   ;

label
   : l = single_label (COMMA l = single_label)*
   ;

single_label
   : (name = IDENT | star = STAR) (LPAREN (string_value (COMMA string_value)*)? RPAREN)?
   ;

