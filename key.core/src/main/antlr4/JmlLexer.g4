
lexer grammar JmlLexer;

@header {}

@members{
   // needed for double literals and ".."
   private int _lex_pos;

   private int parenthesisLevel = 0;
   private void incrParen() { parenthesisLevel++;}
   private void decrParen() { parenthesisLevel--;}

   private int bracesLevel = 0;
   private void incrBrace() { bracesLevel++;}
   private void decrBrace() { bracesLevel--;}

   private int bracketLevel = 0;
   private void incrBracket() { bracketLevel++;}
   private void decrBracket() { bracketLevel--;}

   boolean semicolonOnToplevel() { return bracketLevel==0 && bracesLevel == 0 && parenthesisLevel==0; }

   private JmlMarkerDecision jmlMarkerDecision = new JmlMarkerDecision(this);
}

tokens {BODY, COMMENT, STRING_LITERAL}

MODEL_BEHAVIOUR: 'model_' BEHAVIOR ;
ABSTRACT: 'abstract';
BEHAVIOR: 'behavior'| 'behaviour';
EXCEPTIONAL_BEHAVIOUR: 'exceptional_' BEHAVIOR;
BREAK_BEHAVIOR: 'break_' BEHAVIOR;
CONTINUE_BEHAVIOR: 'continue_' BEHAVIOR;
ALSO: 'also';
CODE_BIGINT_MATH: 'code_bigint_math';
CODE_JAVA_MATH: 'code_java_math';
CODE_SAFE_MATH: 'code_safe_math';
CONST: 'const';
NATIVE: 'native';
NON_NULL: 'non_null';
NORMAL_BEHAVIOR: 'normal_' BEHAVIOR;
NO_STATE: 'no_state' ;
NOWARN: 'nowarn';
NULLABLE: 'nullable';
NULLABLE_BY_DEFAULT: 'nullable_by_default';
SPEC_SAFE_MATH: 'spec_safe_math';
SPEC_BIGINT_MATH: 'spec_bigint_math';
SPEC_JAVA_MATH: 'spec_java_math';
SPEC_PROTECTED: 'spec_protected';
SPEC_PUBLIC: 'spec_public';
GHOST: 'ghost' /*-> pushMode(expr)*/;
SPEC_NAME: 'name'; // ???
STATIC: 'static';
STRICTFP: 'strictfp';
STRICTLY_PURE: 'strictly_pure';
SYNCHRONIZED: 'synchronized';
TRANSIENT: 'transient';
TWO_STATE: 'two_state' ;
UNINITIALIZED: 'uninitialized';
UNREACHABLE: 'unreachable';
VOLATILE: 'volatile';
PRIVATE: 'private';
PROTECTED: 'protected';
PUBLIC: 'public';
PURE: 'pure';
RETURN_BEHAVIOR: 'return_' BEHAVIOR;
FINAL: 'final';
MODEL: 'model'/*  -> pushMode(expr)*/;

fragment Pred: '_redundantly'?; //suffix
fragment Pfree: '_free'?;       //suffix

ACCESSIBLE: 'accessible' Pred -> pushMode(expr);
ASSERT: 'assert' Pred  -> pushMode(expr);
ASSUME: 'assume' Pred -> pushMode(expr);
ASSIGNABLE: ('assignable' | 'assigns' | 'assigning') Pfree -> pushMode(expr);
LOOP_ASSIGNABLE: ('loop_modifies' | 'loop_writes') (Pfree|Pred) -> pushMode(expr);
AXIOM: 'axiom' -> pushMode(expr);
BREAKS: 'breaks' -> pushMode(expr);
CAPTURES: 'captures' Pred -> pushMode(expr);
CODE: 'code'; //?
CONSTRAINT: 'constraint' Pred -> pushMode(expr);
CONTINUES: 'continues' -> pushMode(expr);
DEBUG: 'debug'; //?
DECREASING: ('decreasing' | 'decreases' | 'loop_variant') Pred -> pushMode(expr);
DETERMINES: 'determines' -> pushMode(expr);
DIVERGES: 'diverges' Pred -> pushMode(expr);
//DURATION: 'duration' Pred -> pushMode(expr);
ENSURES: ('ensures' (Pfree|Pred) | 'post' Pred )-> pushMode(expr);
FOR_EXAMPLE: 'for_example' -> pushMode(expr);
//FORALL: 'forall' -> pushMode(expr); //?
HELPER: 'helper';
IMPLIES_THAT: 'implies_that' -> pushMode(expr);
IN: 'in' Pred -> pushMode(expr);
INITIALLY: 'initially' -> pushMode(expr);
INSTANCE: 'instance';
INVARIANT: 'invariant' (Pfree|Pred) -> pushMode(expr);
LOOP_CONTRACT: 'loop_contract';
LOOP_INVARIANT: ('loop_invariant' (Pfree|Pred) | 'maintaining' Pred) -> pushMode(expr);
LOOP_DETERMINES: 'loop_determines';  // internal translation for 'determines' in loop invariants
LOOP_SEPARATES: 'loop_separates';  //KeY extension, deprecated
MAPS: 'maps' Pred -> pushMode(expr);
MEASURED_BY: 'measured_by' Pred -> pushMode(expr);
MERGE_POINT: 'merge_point';
MERGE_PROC: 'merge_proc';
MERGE_PARAMS: 'merge_params' -> pushMode(expr);
MODIFIABLE: 'modifiable' Pred -> pushMode(expr);
MODIFIES: 'modifies' Pred -> pushMode(expr);
MONITORED: 'monitored' -> pushMode(expr);
MONITORS_FOR: 'monitors_for' -> pushMode(expr);
//OLD: 'old' -> pushMode(expr);
//POST: 'post'Pred -> pushMode(expr);
//PRE: 'pre' Pred -> pushMode(expr);
READABLE: 'readable';
REPRESENTS: 'represents' Pred -> pushMode(expr);
REQUIRES: ('requires' (Pfree|Pred) | 'pre' Pred) -> pushMode(expr);
RETURN: 'return' -> pushMode(expr);
RETURNS: 'returns' -> pushMode(expr);
RESPECTS: 'respects' -> pushMode(expr);
SEPARATES: 'separates' -> pushMode(expr);
SET: 'set' -> pushMode(expr);
SIGNALS: ('signals' Pred | 'exsures' Pred) -> pushMode(expr);
SIGNALS_ONLY: 'signals_only' Pred -> pushMode(expr);
WHEN: 'when' Pred -> pushMode(expr);
WORKING_SPACE: 'working_space' Pred -> pushMode(expr);
WRITABLE: 'writable' -> pushMode(expr);

JML_ML_END: '*/' -> channel(HIDDEN);
WS: (' ' | '\t' | '\n' | '\r' | '@')+ -> channel(HIDDEN);
NEST_START: '{|' ;
NEST_END: '|}' ;
C_RBRACKET: ']' -> type(RBRACKET);
C_LBRACKET: '[' -> type(LBRACKET);
SEMICOLON : ';' -> type(SEMI_TOPLEVEL);
C_LBRACE: '{' -> type(LBRACE);
C_RBRACE: '}' -> type(RBRACE);
C_EQUAL: '=' -> type(EQUAL_SINGLE), pushMode(expr);
C_LPAREN: '(' -> type(LPAREN);
C_RPAREN: ')' -> type(RPAREN);
C_STRING_LITERAL: '"' -> pushMode(string), more;
C_IDENT: '\\'? LETTER (LETTERORDIGIT)* -> type(IDENT);
C_COLON: ':' -> type(COLON);
C_DOT: '.' -> type(DOT);
C_COMMA: ',' -> type(COMMA);

SL_COMMENT: {jmlMarkerDecision.isComment("//")}? ('//' ('\n'|'\r'|EOF) | '//' ~'@' ~('\n'|'\r')*) -> channel(HIDDEN);
ML_COMMENT: {jmlMarkerDecision.isComment("/*")}? '/*' -> more, pushMode(mlComment);

JML_SL_START: {!jmlMarkerDecision.isComment("//")}? '//' ([+-] [a-zA-Z_0-9]*)* '@' -> channel(HIDDEN);
JML_ML_START: {!jmlMarkerDecision.isComment("/*")}?'/*' ([+-] [a-zA-Z_0-9]*)* '@' -> channel(HIDDEN);

ERROR_CHAR: .;

mode expr;

/* Java keywords */
BOOLEAN: 'boolean';
BYTE: 'byte';
FALSE: 'false';
INSTANCEOF: 'instanceof';
INT: 'int';
LONG: 'long';
NEW: 'new';
NULL: 'null';
SHORT: 'short';
SUPER: 'super';
THIS: 'this';
TRUE: 'true';
VOID: 'void';

E_NULLABLE: 'nullable'->type(NULLABLE);
E_NONNULL: 'non_null' -> type(NON_NULL);


DEPENDS: 'depends';  // internal translation for 'accessible' on model fields

/* JML and JML* keywords */
/*ACCESSIBLE: 'accessible';
ASSIGNABLE: 'assignable';
BREAKS: 'breaks';
CONTINUES: 'continues';
DECREASES: 'decreases'; // internal translation for 'measured_by'
DETERMINES: 'determines';  //KeY extension, not official JML
ENSURES: 'ensures';
ENSURES_FREE: 'ensures_free';
MODEL_METHOD_AXIOM: 'model_method_axiom';  //KeY extension, not official JML
MERGE_PARAMS: 'merge_params';  //KeY extension, not official JML
NON_NULL: 'non_null';
NULLABLE: 'nullable';
REPRESENTS: 'represents';
REQUIRES: 'requires';
REQUIRES_FREE: 'requires_free';
RETURNS: 'returns';  //KeY extension, not official JML
SEPARATES: 'separates';  //KeY extension, not official JML
SIGNALS: 'signals';
SIGNALS_ONLY: 'signals_only';*/

/* JML keywords prefixed with a backslash */
ALLFIELDS: '\\all_fields';  //KeY extension, not official JML
ALLOBJECTS: '\\all_objects';  //KeY extension, not official JML
BACKUP: '\\backup';  //KeY extension, not official JML
BEFORE: '\\before';  //KeY extension, not official JML
BIGINT: '\\bigint';
BSUM: '\\bsum';  //KeY extension, not official JML
BY: '\\by';  //KeY extension, not official JML
DECLASSIFIES: '\\declassifies';  //KeY extension, not official JML
DISJOINT: '\\disjoint';  //KeY extension, not official JML
DOMAIN_IMPLIES_CREATED: '\\domain_implies_created';  //KeY extension, not official JML
DURATION: '\\duration';
ELEMTYPE: '\\elemtype';
EMPTYSET: '\\empty';
ERASES: '\\erases';  //KeY extension, not official JML
EVERYTHING: '\\everything';
EXCEPTION: '\\exception';
EXISTS: '\\exists';
FORALL: '\\forall';
FP_ABS: '\\fp_abs';  //KeY extension, not official JML
FP_INFINITE : '\\fp_infinite';   //KeY extension, not official JML
FP_NAN: '\\fp_nan';   //KeY extension, not official JML
FP_NEGATIVE: '\\fp_negative';   //KeY extension, not official JML
FP_NICE: '\\fp_nice'; //KeY syntactic sugar
FP_NORMAL: '\\fp_normal';   //KeY extension, not official JML
FP_POSITIVE: '\\fp_positive';   //KeY extension, not official JML
FP_SUBNORMAL: '\\fp_subnormal';   //KeY extension, not official JML
FP_ZERO: '\\fp_zero';   //KeY extension, not official JML
FREE: '\\free';  //KeY extension, not official JML
FRESH: '\\fresh';
INDEX: '\\index';
INDEXOF: '\\seq_indexOf';  //KeY extension, not official JML
INTERSECT: '\\intersect';  //KeY extension, not official JML
INTO: '\\into';
INV: '\\inv';  //KeY extension, not official JML
INV_FREE: '\\inv_free';  //KeY extension, not official JML
INVARIANT_FOR: '\\invariant_for';
INVARIANT_FREE_FOR: '\\invariant_free_for';  //KeY extension, not official JML
IN_DOMAIN: '\\in_domain';  //KeY extension, not official JML
IS_FINITE: '\\is_finite';  //KeY extension, not official JML
IS_INITIALIZED: '\\is_initialized';
ITSELF: '\\itself';  //KeY extension, not official JML
LBLNEG: '\\lblneg';
LBLPOS: '\\lblpos';
LOCKSET: '\\lockset';
LOCSET: '\\locset';  //KeY extension, not official JML
STOREREF: '\\storeref';  //KeY extension, not official JML
MAP: '\\map';  //KeY extension, not official JML
MAPEMPTY: '\\map_empty';  //KeY extension, not official JML
MAP_GET: '\\map_get';  //KeY extension, not official JML
MAP_OVERRIDE: '\\map_override';  //KeY extension, not official JML
MAP_REMOVE: '\\map_remove';  //KeY extension, not official JML
MAP_SINGLETON: '\\map_singleton';  //KeY extension, not official JML
MAP_SIZE: '\\map_size';  //KeY extension, not official JML
MAP_UPDATE:  '\\map_update';  //KeY extension, not official JML
MAX: '\\max';
E_MEASURED_BY: '\\measured_by' -> type(MEASURED_BY);
MIN: '\\min';
NEWELEMSFRESH: '\\new_elems_fresh';  //KeY extension, not official JML
NEW_OBJECTS: '\\new_objects';  //KeY extension, not official JML
NONNULLELEMENTS: '\\nonnullelements';
NOTHING: '\\nothing';
NOT_ASSIGNED: '\\not_assigned';
NOT_MODIFIED: '\\not_modified';
NOT_SPECIFIED: '\\not_specified';
NUM_OF: '\\num_of';
OLD: '\\old';
JAVA_MATH: '\\java_math';
SAFE_MATH: '\\safe_math';
BIGINT_MATH: '\\bigint_math';
PERMISSION: '\\permission';
PRE: '\\pre';
PRODUCT: '\\product';
REACH: '\\reach';
REACHLOCS: '\\reachLocs';  //KeY extension, not official JML
REAL: '\\real';
RESULT: '\\result';
SAME: '\\same';
SEQ: '\\seq';  //KeY extension, not official JML
SEQ2MAP: '\\seq_2_map';  //KeY extension, not official JML
SEQCONCAT: '\\seq_concat';  //KeY extension, not official JML
SEQDEF: '\\seq_def';  //KeY extension, not official JML
SEQEMPTY: '\\seq_empty';  //KeY extension, not official JML
SEQGET: '\\seq_get';  //KeY extension, not official JML
SEQREPLACE: '\\seq_put';  //KeY extension, not official JML
SEQREVERSE: '\\seq_reverse';  //KeY extension, not official JML
SEQSINGLETON: '\\seq_singleton';  //KeY extension, not official JML
SEQSUB: '\\seq_sub';  //KeY extension, not official JML
SETMINUS: '\\set_minus';  //KeY extension, not official JML
SINGLETON: '\\singleton';  //KeY extension, not official JML
SPACE: '\\space';
STATIC_INVARIANT_FOR: '\\static_invariant_for';  //KeY extension, not official JML
STATIC_INVARIANT_FREE_FOR: '\\static_invariant_free_for';  //KeY extension, not official JML
STRICTLY_NOTHING: '\\strictly_nothing';  //KeY extension, not official JML
STRING_EQUAL: '\\string_equal';  //KeY extension, not official JML
SUBSET: '\\subset';
SUCH_THAT: '\\such_that';
SUM: '\\sum';
TRANSACTIONUPDATED: '\\transactionUpdated';  //KeY extension, not official JML
E_TRANSIENT: '\\transient' -> type(TRANSIENT);  //KeY extension, not official JML
TYPE: '\\TYPE';
TYPEOF: '\\typeof';
TYPE_SMALL: '\\type';
UNION: '\\set_union';  //KeY extension, not official JML
UNIONINF: '\\infinite_union';  //KeY extension, not official JML
VALUES: '\\values';
WORKINGSPACE: '\\working_space';
// ONLY_ACCESSED: '\\only_accessed'; // too many common lexemes
// ONLY_ASSIGNED: '\\only_assigned';
// ONLY_CALLED: '\\only_called';
// ONLY_CAPTURED: '\\only_captured';

E_JML_SL_START: '//@' -> type(JML_SL_START), channel(HIDDEN);
E_JML_ML_START: '/*@' -> type(JML_ML_START), channel(HIDDEN);
E_JML_ML_END: '*/' -> channel(HIDDEN);
E_SL_COMMENT: {jmlMarkerDecision.isComment("//")}? ('//' ('\n'|'\r'|EOF) | '//' ~'@' ~('\n'|'\r')*) -> type(COMMENT), channel(HIDDEN);
E_ML_COMMENT: {jmlMarkerDecision.isComment("/*")}? '/*' -> more, pushMode(mlComment);

AND: '&';
BITWISENOT: '~';
COLON: ':';
COMMA: ',';
DIV: '/';
DOT: '.';
DOTDOT: '..';
EQUAL_SINGLE: '=';
EQV_ANTIV: '<==>' | '<=!=>';
EQ_NEQ: '==' | '!=';
GEQ: '>=';
IMPLIES: '==>';
IMPLIESBACKWARD: '<==';
INCLUSIVEOR: '|';
LARROW: '<-';
LEQ: '<=';
LOCKSET_LEQ: '<#=';
LOCKSET_LT: '<#';
LOGICALAND: '&&';
LOGICALOR: '||';
MINUS: '-';
MOD: '%';
MULT: '*';
NOT: '!';
PLUS: '+';
QUESTIONMARK: '?';
RARROW: '->';
SHIFTLEFT: '<<';
SHIFTRIGHT: '>>';
ST: '<:';
UNSIGNEDSHIFTRIGHT: '>>>';
XOR: '^';
GT: '>';
LT: '<';


LPAREN:               '(' {incrParen();};
RPAREN:               ')' {decrParen();};
LBRACE:               '{' {incrBrace();};
RBRACE:               '}' {decrBrace();};
LBRACKET:             '[' {incrBracket();};
RBRACKET:             ']' {decrBracket();};
SEMI_TOPLEVEL:        {   semicolonOnToplevel()}? ';' -> popMode; //jump back to contract mode
SEMI:                 { ! semicolonOnToplevel()}? ';';

fragment LETTER: 'a'..'z' | 'A'..'Z' | '_' | '$';


fragment BINDIGIT: '0'..'1';
fragment OCTDIGIT: '0'..'7';
fragment NONZERODECDIGIT: '1'..'9';
fragment DECDIGIT: '0'..'9';
fragment DIGIT: '0'..'9';
fragment HEXDIGIT:  DIGIT | 'a' .. 'f' | 'A' .. 'F';
fragment BINPREFIX: '0' ('b'|'B');
fragment OCTPREFIX: '0';
fragment HEXPREFIX: '0' ('x'|'X');
fragment LONGSUFFIX: 'l' | 'L';

BINLITERAL: BINPREFIX BINDIGIT ((BINDIGIT | '_')* BINDIGIT)? LONGSUFFIX?;
OCTLITERAL: OCTPREFIX OCTDIGIT ((OCTDIGIT | '_')* OCTDIGIT)? LONGSUFFIX?;
DECLITERAL: ('0' | (NONZERODECDIGIT ((DECDIGIT | '_')* DECDIGIT)?)) LONGSUFFIX?;
HEXLITERAL: HEXPREFIX ((HEXDIGIT | '_')* HEXDIGIT)? LONGSUFFIX?;

fragment
FractionalNumber
    :   DIGIT+ '.' DIGIT* Exponent?
    |   '.' DIGIT+ Exponent?
    |   DIGIT+ Exponent?
    ;

fragment
Exponent
    :   ( 'e' | 'E' ) ( '+' | '-' )? ( '0' .. '9' )+
    ;

fragment
FloatSuffix
    :   'f' | 'F'
    ;

fragment
DoubleSuffix
    :   'd' | 'D'
    ;

fragment
RealSuffix
    :   'r' | 'R'
    ;

FLOAT_LITERAL
    :   FractionalNumber FloatSuffix
    ;

REAL_LITERAL
    :   FractionalNumber RealSuffix
    ;

DOUBLE_LITERAL
    :  /*  MU2018: DIGITS was removed, the following was not accessible.
        *  It is strange anyway ...
        *  MU2019: But necessary, since otherwise 1..x would be parsed as (1.).x
        *  MU2021: Brought to ANTLR4 as by
        *     https://stackoverflow.com/questions/35724082/syntactic-predicates-in-antlr-lexer-rules
        */
        DIGIT+ '.' DIGIT+ Exponent? DoubleSuffix?
    |   DIGIT+ '.'? Exponent DoubleSuffix?
    |   DIGIT+ '.' DoubleSuffix
    |   '.' DIGIT+ Exponent? DoubleSuffix?
    |   DIGIT+ Exponent DoubleSuffix?
    |   DIGIT+  { _lex_pos=_input.index(); setType(DECLITERAL); emit(); }
         '.' '.' { _input.seek(_lex_pos); }
    |   DIGIT+ '.'
    ;


fragment
LETTERORDIGIT: LETTER | DIGIT;

IDENT: LETTER (LETTERORDIGIT)*;
JML_IDENT: '\\' IDENT ;
SPECIAL_IDENT: '<'IDENT'>';

//DL_ESCAPE: '\\dl_'  LETTER  ( LETTERORDIGIT )*  ;

/*
HEXLITERAL:
        '0' ('x'|'X') (HEXDIGIT)+ ( 'l'|'L' )?
    ;

OCTLITERAL:
        '0' (DIGIT)+ ( 'l'|'L' )?
    ;

DECLITERAL:
        (('1'..'9') (DIGIT)* | '0') ( 'l'|'L' )?
    ;
*/

CHAR_LITERAL:
        '\''
                (~('\''|'\\') |
                 ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | OCT_CHAR
                 | 'u' HEXDIGIT HEXDIGIT HEXDIGIT HEXDIGIT )) //add for safety
                 // note: unicode escapes are processed earlier
                )
      '\''
    ;

fragment OCT_CHAR:
        (('0'|'1'|'2'|'3') OCTDIGIT OCTDIGIT) | (OCTDIGIT OCTDIGIT) | OCTDIGIT;

STRING_LITERAL: '"' -> pushMode(string),more;
E_WS: [ \t\n\r\u000c@]+ -> channel(HIDDEN), type(WS);
INFORMAL_DESCRIPTION: '(*'  ( '*' ~')' | ~'*' )* '*)';

DOC_COMMENT: '/**' -> pushMode(mlComment);
fragment PRAGMA: '\\nowarn';

E_ERROR_CHAR: . -> type(ERROR_CHAR);

mode mlComment;
ML_COMMENT_END: ('*/'|EOF) -> type(COMMENT), channel(HIDDEN), popMode;
ML_ANY: . -> more;

mode string;
S_ESC: '\\"' -> more;
S_END: '"' -> type(STRING_LITERAL), popMode;
S_ANY: . -> more;
