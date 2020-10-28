grammar SMTProof;

smtoutput : ('Result: valid' 'unsat')? proof;

proof
    : LPAREN command* LPAREN 'proof' proofsexpr+ RPAREN RPAREN EOF
    // with pretty proof option, the enclosing 'proof' term is missing
    | proofsexpr EOF
    ;

proofsexpr
    : LPAREN rulename=PROOFRULE proofsexpr+ RPAREN
    | LPAREN LPAREN UNDERSCORE rulename=PROOFRULE proofsexpr+ RPAREN proofsexpr+ RPAREN
    | LPAREN rulename=LET LPAREN var_binding+ RPAREN proofsexpr RPAREN          // shared subtree of proof
    | LPAREN rulename=LAMBDA LPAREN sorted_var+ RPAREN proofsexpr RPAREN     // TODO: single proofsexpr should be enough (originally had proofsexpr+)
    | LPAREN MATCH proofsexpr LPAREN match_case+ RPAREN RPAREN
    //| LPAREN EXCL proofsexpr attribute+ RPAREN
    | noproofterm
    ;

/** term that does not contain nested proof rules (just a "normal" SMT term with functions/constants) */
noproofterm
    : spec_constant
    | qual_identifier
    | LPAREN func=noproofterm noproofterm+ RPAREN
    | LPAREN quant=FORALL LPAREN sorted_var+ RPAREN noproofterm RPAREN
    | LPAREN quant=EXISTS LPAREN sorted_var+ RPAREN noproofterm RPAREN
    | LPAREN rulename=LET LPAREN var_binding+ RPAREN noproofterm RPAREN         // shared formula/term
    | LPAREN MATCH noproofterm LPAREN match_case+ RPAREN RPAREN
    | LPAREN EXCL noproofterm attribute+ RPAREN
    ;

function_def : SYMBOL LPAREN sorted_var* RPAREN sort term ;

command
    : LPAREN cmdName=ASSERT term RPAREN
    | LPAREN cmdName=CHECK_SAT RPAREN
    | LPAREN cmdName=DECL_CONST SYMBOL sort RPAREN
    | LPAREN cmdName=DECL_FUN SYMBOL LPAREN sort* RPAREN sort RPAREN
    | LPAREN cmdName=DEF_FUN function_def RPAREN
    | LPAREN cmdName=EXIT RPAREN
    | LPAREN cmdName=GET_PROOF RPAREN
    | LPAREN cmdName=SET_LOGIC SYMBOL RPAREN
    //| LPAREN SET_OPTION option RPAREN
    ;

spec_constant : NUM | DECIMAL | HEX | BIN | STRING ;

s_expr
    : spec_constant
    | SYMBOL
    | KEYWORD
    | LPAREN s_expr* RPAREN
 //   | LPAREN EXCL s_expr attribute+ RPAREN
    ;

qual_identifier : identifier | LPAREN AS identifier sort RPAREN ;

identifier
    : SYMBOL
    | LPAREN UNDERSCORE SYMBOL INDEX+ RPAREN
    ;

sort : identifier | LPAREN identifier sort+ RPAREN ;

attribute_value : spec_constant | SYMBOL | LPAREN s_expr* RPAREN ;
attribute : KEYWORD | KEYWORD attribute_value ;

var_binding : LPAREN SYMBOL proofsexpr RPAREN ;
//var_binding_noproof : LPAREN SYMBOL noproofterm RPAREN ;
sorted_var : LPAREN SYMBOL sort RPAREN ;
pattern : SYMBOL | LPAREN SYMBOL SYMBOL+ RPAREN ;
match_case : LPAREN pattern term LPAREN ;
term
    : spec_constant
    | qual_identifier
    //| LPAREN qual_identifier term+ RPAREN
    | LPAREN term term+ RPAREN
    //| LPAREN 'lambda' LPAREN sorted_var+ RPAREN term+ RPAREN
    //| LPAREN LET LPAREN var_binding+ RPAREN term RPAREN
    | LPAREN FORALL LPAREN sorted_var+ RPAREN term RPAREN
    | LPAREN EXISTS LPAREN sorted_var+ RPAREN term RPAREN
    | LPAREN MATCH term LPAREN match_case+ RPAREN RPAREN
    | LPAREN EXCL term attribute+ RPAREN
    ;

LPAREN : '(' ;
RPAREN : ')' ;

// minimum proof rules for large proof example
PROOFRULE
    : PR_ASSERTED
    | PR_MODUS_PONENS
    | PR_REFLEXIVITY
    | PR_SYMMETRY
    | PR_TRANSITIVITY
    | PR_TRANSITIVITY_STAR
    | PR_MONOTONICITY
    | PR_QUANT_INTRO
    | PR_BIND
    | PR_AND_ELIM
    | PR_NOT_OR_ELIM
    | PR_REWRITE
    | PR_REWRITE_STAR
    | PR_PULL_QUANT
    | PR_PUSH_QUANT
    | PR_QUANT_INST
    | PR_HYPOTHESIS
    | PR_LEMMA
    | PR_UNIT_RESOLUTION
    | PR_IFF_TRUE
    | PR_IFF_FALSE
    | PR_COMMUTATIVITY
    | PR_DEF_AXIOM
    | PR_NNF_POS
    | PR_NNF_NEG
    | PR_SKOLEMIZE
    | PR_MODUS_PONENS_OEQ
    | PR_TH_LEMMA
    ;

PR_UNDEF :              'undef';
PR_TRUE :               'true-axiom';
PR_ASSERTED :           'asserted' ;
PR_GOAL :               'goal';
PR_MODUS_PONENS :       'mp' ;
PR_REFLEXIVITY :        'refl';
PR_SYMMETRY :           'symm' ;
PR_TRANSITIVITY :       'trans' ;
PR_TRANSITIVITY_STAR :  'trans*' ;
PR_MONOTONICITY :       'monotonicity' ;
PR_QUANT_INTRO :        'quant-intro' ;
PR_BIND :               'proof-bind';
PR_DISTRIBUTIVITY :     'distributivity';
PR_AND_ELIM :           'and-elim';
PR_NOT_OR_ELIM :        'not-or-elim';
PR_REWRITE :            'rewrite' ;
PR_REWRITE_STAR :       'rewrite*' ;
PR_PULL_QUANT :         'pull-quant';
PR_PUSH_QUANT :         'push-quant';
PR_ELIM_UNUSED_VARS :   'elim-unused';
PR_DER :                'der';
PR_QUANT_INST :         'quant-inst';
PR_HYPOTHESIS :         'hypothesis';
PR_LEMMA :              'lemma';
PR_UNIT_RESOLUTION :    'unit-resolution';
PR_IFF_TRUE :           'iff-true';
PR_IFF_FALSE :          'iff-false';
PR_COMMUTATIVITY :      'commutativity';
PR_DEF_AXIOM :          'def-axiom';
PR_ASSUMPTION_ADD :     'add-assume';
PR_LEMMA_ADD :          'add-lemma';
PR_REDUNDANT_DEL :      'del-redundant';
PR_CLAUSE_TRAIL :       'proof-trail';
PR_DEF_INTRO :          'intro-def';
PR_APPLY_DEF :          'apply-def';
PR_IFF_OEQ :            'iff~';
PR_NNF_POS :            'nnf-pos';
PR_NNF_NEG :            'nnf-neg';
PR_SKOLEMIZE :          'sk';
PR_MODUS_PONENS_OEQ :   'mp~';
PR_TH_LEMMA :           'th-lemma' ;
PR_HYPER_RESOLVE :      'hyper-res';

// commands
// TODO: missing commands
ASSERT :        'assert' ;
CHECK_SAT :     'check-sat' ;
DECL_CONST :    'declare-const' ;
DECL_FUN :      'declare-fun' ;
DEF_FUN :       'define-fun' ;
EXIT :          'exit' ;
GET_PROOF :     'get-proof' ;
SET_LOGIC :     'set-logic' ;
SET_OPTION :    'set-option' ;

// reserved words
// TODO: BINARY, DECIMAL, HEXADECIMAL, NUMERAL, STRING
UNDERSCORE : '_';
EXCL : '!' ;
AS : 'as' ;
LET : 'let' ;
LAMBDA : 'lambda' ;
EXISTS : 'exists' ;
FORALL : 'forall' ;
MATCH : 'match' ;
PAR : 'par' ;

fragment Digit
      : [0-9]
      ;

fragment HexDigit
      : [0-9a-fA-F]
      ;

fragment Sym
      : 'a'..'z'
      | 'A' .. 'Z'
      | '~'
      | '!'
      | '@'
      | '$'
      | '%'
      | '^'
      | '&'
      | '*'
      | '_'
      | '-'
      | '+'
      | '='
      | '<'
      | '>'
      | '.'
      | '?'
      | '/'
      ;

NUM : Digit+ ;
DECIMAL : NUM '.' '0'* NUM ;
HEX : '#x' HexDigit+ ;
BIN : '#b' [0|1]+ ;

//ID  : Sym (Digit | Sym)* ;
fragment SIMPLE_SYMBOL : Sym (Digit | Sym)*;
fragment ESCAPED_SYMBOL : '|' .*? '|' ;
KEYWORD : ':' SIMPLE_SYMBOL ;
SYMBOL : SIMPLE_SYMBOL | ESCAPED_SYMBOL ;
INDEX : NUM | SYMBOL ;
// TODO: escaping " is allowed : """" is a valid string denoting "
STRING : '"' .*? '"' ;

WS : [ \t\r\n]+ -> channel(HIDDEN) ;
COMMENT : ';' .*? '\n' -> skip ;

ANY : . ;