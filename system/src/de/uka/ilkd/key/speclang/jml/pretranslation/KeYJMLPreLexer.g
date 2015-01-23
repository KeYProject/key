// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

lexer grammar KeYJMLPreLexer;


@header {
    package de.uka.ilkd.key.speclang.jml.pretranslation;

    import de.uka.ilkd.key.util.Debug;
}

@annotateclass{ @SuppressWarnings("all") } 

@members {
    private void newline() {
      Debug.out("newline() was called but ANTLRv3 does not implement it anymore.");
    }

    private void append(final String text) {
      setText(getText() + text);
    }
}

    ABSTRACT 			: 'abstract';
    ACCESSIBLE                  : 'accessible';
    ACCESSIBLE_REDUNDANTLY      : 'accessible_redundantly';
    ALSO 			: 'also';
    ASSERT                      : 'assert';
    ASSERT_REDUNDANTLY          : 'assert_redundantly';
    ASSUME                      : 'assume';
    ASSUME_REDUNDANTLY          : 'assume_redundantly';
    ASSIGNABLE 			: 'assignable';
    ASSIGNABLE_RED 		: 'assignable_redundantly';
    AXIOM                       : 'axiom';
    BEHAVIOR 			: 'behavior';
    BEHAVIOUR 			: 'behaviour';
	BREAKS				: 'breaks';
	BREAK_BEHAVIOR 	    : 'break_behavior';
    BREAK_BEHAVIOUR 	: 'break_behaviour';
    CAPTURES 			: 'captures';
    CAPTURES_RED 		: 'captures_redundantly';
    CODE 			: 'code';
    CODE_BIGINT_MATH 		: 'code_bigint_math';
    CODE_JAVA_MATH 		: 'code_java_math';
    CODE_SAFE_MATH		: 'code_safe_math';
    CONST 			: 'const';
    CONSTRAINT			: 'constraint';
    CONSTRAINT_RED		: 'constraint_redundantly';
	CONTINUES			: 'continues';
	CONTINUE_BEHAVIOR 	: 'continue_behavior';
    CONTINUE_BEHAVIOUR 	: 'continue_behaviour';
    DEBUG   : 'debug';
    DECREASES  			: 'decreases';
    DECREASES_REDUNDANTLY  	: 'decreases_redundantly';
    DECREASING  		: 'decreasing';
    DECREASING_REDUNDANTLY  	: 'decreasing_redundantly';
    DETERMINES                  : 'determines';
    DIVERGES 			: 'diverges';
    DIVERGES_RED 		: 'diverges_redundantly';
    DURATION 			: 'duration';
    DURATION_RED 		: 'duration_redundantly';
    ENSURES 			: 'ensures';
    ENSURES_RED 		: 'ensures_redundantly';
    EXCEPTIONAL_BEHAVIOR 	: 'exceptional_behavior';
    EXCEPTIONAL_BEHAVIOUR 	: 'exceptional_behaviour';
    EXSURES                     : 'exsures';
    EXSURES_RED                 : 'exsures_redundantly';
    FINAL 			: 'final';
    FOR_EXAMPLE			: 'for_example';
    FORALL			: 'forall';
    GHOST 			: 'ghost';
    HELPER 			: 'helper';
    IMPLIES_THAT		: 'implies_that';
    IN				: 'in';
    IN_RED			: 'in_redundantly';
    INITIALLY			: 'initially';
    INSTANCE 			: 'instance';
    INVARIANT 			: 'invariant';
    INVARIANT_RED 		: 'invariant_redundantly';
    LOOP_INVARIANT  		: 'loop_invariant';
    LOOP_INVARIANT_RED  	: 'loop_invariant_redundantly';
    MAINTAINING  		: 'maintaining';
    MAINTAINING_REDUNDANTLY	: 'maintaining_redundantly';
    MAPS			: 'maps';
    MAPS_RED			: 'maps_redundantly';
    MEASURED_BY                 : 'measured_by';
    MEASURED_BY_REDUNDANTLY     : 'measured_by_redundantly';
    MODEL 			: 'model';
    MODEL_BEHAVIOR 		: 'model_behavior' ;
    MODEL_BEHAVIOUR 		: 'model_behaviour' ;
    MODIFIABLE			: 'modifiable';
    MODIFIABLE_RED		: 'modifiable_redundantly';
    MODIFIES			: 'modifies';
    MODIFIES_RED		: 'modifies_redundantly';
    MONITORED                   : 'monitored';
    MONITORS_FOR		: 'monitors_for';
    NATIVE			: 'native';
    NON_NULL 			: 'non_null';
    NORMAL_BEHAVIOR 		: 'normal_behavior';
    NORMAL_BEHAVIOUR 		: 'normal_behaviour';
    NO_STATE			: 'no_state' ;
    NOWARN			: 'nowarn';
    NULLABLE 			: 'nullable';
    NULLABLE_BY_DEFAULT 	: 'nullable_by_default';
    OLD				: 'old';
    POST    : 'post';
    POST_RED  : 'post_redundantly';
    PRE     : 'pre';
    PRE_RED : 'pre_redundantly';
    PRIVATE 			: 'private';
    PROTECTED 			: 'protected';
    PUBLIC			: 'public';
    PURE 			: 'pure';
    STRICTLY_PURE               : 'strictly_pure';
    READABLE			: 'readable';
    REPRESENTS			: 'represents';
    REPRESENTS_RED		: 'represents_redundantly';
    REQUIRES 			: 'requires';
    REQUIRES_RED 		: 'requires_redundantly';
	RETURNS				: 'returns';
	RETURN_BEHAVIOR 	: 'return_behavior';
    RETURN_BEHAVIOUR 	: 'return_behaviour';
    RESPECTS                    : 'respects';
    SEPARATES                   : 'separates';
    SET 			: 'set';
    SIGNALS 			: 'signals';
    SIGNALS_ONLY 		: 'signals_only';
    SIGNALS_ONLY_RED 		: 'signals_only_redundantly';
    SIGNALS_RED 		: 'signals_redundantly';
    SPEC_BIGINT_MATH 		: 'spec_bigint_math';
    SPEC_JAVA_MATH 		: 'spec_java_math';
    SPEC_PROTECTED 		: 'spec_protected';
    SPEC_PUBLIC 		: 'spec_public';
    SPEC_NAME                   : 'name'; // ???
    SPEC_SAFE_MATH 		: 'spec_safe_math';
    STATIC 			: 'static';
    STRICTFP 			: 'strictfp';
    SYNCHRONIZED 		: 'synchronized';
    TRANSIENT 			: 'transient';
    TWO_STATE			: 'two_state' ;
    UNINITIALIZED 		: 'uninitialized';
    UNREACHABLE   : 'unreachable';
    VOLATILE 			: 'volatile';
    WHEN 			: 'when';
    WHEN_RED 			: 'when_redundantly';
    WORKING_SPACE 		: 'working_space';
    WORKING_SPACE_RED 		: 'working_space_redundantly';
    WRITABLE			: 'writable';

fragment SL_COMMENT
:
    '//'
    (
	(~('@'|'\n'))
	=>
        ~('@'|'\n')
        (
            options { greedy = true; }
            :
            ~'\n'
        )*
    )?
;


fragment ML_COMMENT
:
    '/*'
    (
        (~('*').|'*'~'/')
        =>
        (	'\n'         { newline(); }
            | 	~('@' | '\n')
        )
	(
	    options { greedy = false; }
            :
                '\n'     { newline(); }
            |	~'\n'
	)*
    )?
    '*/'
;

fragment LETTER
:
        'a'..'z'
    |   'A'..'Z'
    |   '_'
    |   '$'
    |   '\\'
;


fragment DIGIT
:
    '0'..'9'
;


WS
@init {
    boolean acceptAt = false;
}
:
    (
	    ' '
	|   '\t'
	|   '\n'  { newline(); acceptAt = true; }
	|   '\r'
	|   {acceptAt}? '@'
	|   ('//@') => '//@'
	|   ('/*@') => '/*@'
	|   ('@*/') => '@*/'
	|   ('*/') => '*/'
	|   SL_COMMENT
	|   ML_COMMENT
    )+
    {
	$channel = HIDDEN;
    }
;




IDENT
:
    LETTER
    (	options { greedy = true; }
	:
	    LETTER
	|   DIGIT
    )*
;

fragment NEST_START : '{' '|' ;
NEST_END : '|}' ;

fragment BODY
@init {
    int braceCounter = 0;
    boolean ignoreAt = false;
    String s = null;
}
:
   '{'
      (
	   '{'                    { braceCounter++; ignoreAt = false; }
    	|  {braceCounter > 0}?=> '}'  { braceCounter--; ignoreAt = false; }
    	|  '\n'                     { newline(); ignoreAt = true; }
    	|  ' '
    	|  '\u000C'
    	|  '\t'
    	|  '\r'
    	|  {!ignoreAt}? '@'
    	|  {ignoreAt}? { s = getText(); } '@'	    { setText(s); ignoreAt = false; }
    	|  ~('{' | '}' | '\n' | ' ' | '\u000C' | '\t' | '\r' | '@' )    { ignoreAt = false; }
    )* {braceCounter == 0}?=> '}'
;

BRACE_DISPATCH :
   ( '{' ~ '|') => BODY { $type = BODY; }
 | NEST_START { $type = NEST_START; }
 ;

SEMICOLON
:
    ';'
;

STRING_LITERAL
@after {
    // strip quotation marks
    final String text = getText();
    final int length = text.length();
    setText(text.substring(1, length - 1));
}
    : '"' ( ESC | ~('"'|'\\') )* '"'
    ;

fragment
ESC
    :	'\\'
    (	'n'         { setText("\n"); }
	|	'r' { setText("\r"); }
	|	't' { setText("\t"); }
	|	'b' { setText("\b"); }
	|	'f' { setText("\f"); }
	|	'"' { setText("\""); }
	|	'\'' { setText("'"); }
	|	'\\' { setText("\\"); }
	|	':' { setText ("\\:"); }
	|	' ' { setText ("\\ "); }
    )
    ;


    AXIOM_NAME_BEGIN
        :
        '['
        ;

    AXIOM_NAME_END
        :
        ']'
        ;
        
    
// http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_4.html#SEC31, 2013-06-22
    
    

        
LPAREN : '(';
RPAREN : ')';
EQUALITY : '=';
EMPTYBRACKETS : '[]';
        

COMMA : ',' ;
DOT : '.' ;

JAVAOPERATOR
    :
          '='  | '<'   | '>'   | '!'   | '~'    | '?'  | ':'  | '=='
        | '<=' | '>='  | '!='  | '&&'  | '||'   | '++' | '--' | '+'
        | '-'  | '*'   | '/'   | '&'   | '|'    | '^'  | '%'  | '<<'
        | '>>' | '>>>' | '+='  | '-='  | '*='   | '/=' | '&=' | '|='
        | '^=' | '%='  | '<<=' | '>>=' | '>>>='
    ;


JMLSPECIALSYMBOL
    :
          '==>' | '<==' | '<==>' | '<=!=>' | '->' | '<-' | '..' 
    ;

INTEGERLITERAL
    :
        '0' | DECIMALINTEGERLITERAL | HEXINTEGERLITERAL | OCTALINTEGERLITERAL
    ;

fragment
DECIMALINTEGERLITERAL
    :
        NONZERODIGIT DIGITS? INTEGERTYPESUFFIX?
    ;

fragment
HEXINTEGERLITERAL
    :
        HEXNUMERAL INTEGERTYPESUFFIX?
    ;

fragment
HEXNUMERAL
    :
        ('0x' | '0X') HEXDIGIT HEXDIGIT*
    ;

fragment
HEXDIGIT
    :
        DIGIT | 'a'..'f' | 'A'..'F'
    ;

fragment
OCTALINTEGERLITERAL
    :
        OCTALNUMERAL INTEGERTYPESUFFIX?
    ;

fragment
OCTALNUMERAL
    :
        '0' OCTALDIGIT OCTALDIGIT*
    ;

fragment
OCTALDIGIT
    :
        '0'..'7'
    ;

fragment
DIGITS
    :
        DIGIT DIGIT*
    ;

fragment
NONZERODIGIT
    :
        '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
    ;

fragment
INTEGERTYPESUFFIX
    :
        'l' | 'L'
    ;
