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
import java.util.*;
import java.util.regex.*;
}

@members {
    /**
	 * Lookahead for determining if we are at the start of comment and not a "JML starter".
	 * <p>
	 * This method reads from the input stream to check the annotation markers between the
	 * comment start and the "@"
	 * This method returns true for starter "//" if we the comment begins with
	 * <ul>
	 * <li> "//" + End-of-line
	 * <li> "// "
	 * <li> "// @"
	 * <li> "//+"
	 * <li> "//-"
	 * <li> "//-key+openjml@"  (or similar)
	 * </ul>
	 * <p>
	 * (same for "/*")
	 * <p>
	 * It returns true if starter is followed by a sequence of "+", "-" or Java identifier
	 * characters, and then "@" and the sequence does not contain "-key".
	 * <p>
	 * It implements JML Ref Manual 4.4:
	 * <quote>
	 * An annotation-key is a + or - sign followed by an ident (see section 4.6 Tokens). Note that
	 * no white space can appear within, before, or after the annotation-key. Tools will provide a
	 * way to enable a selection of annotation-key identifiers. These identifiers, hereafter called
	 * "keys" provide for conditional inclusion of JML annotations as follows:
	 * <ul>
	 * <li> a JML annotation with no keys is always included,
	 * <li> a JML annotation with at least one positive-key is only included if at least one of
	 * these positive keys is enabled and there are no negative-keys in the annotation that have
	 * enabled keys, and
	 * <li> a JML annotation with an enabled negative-key is ignored (even if there are enabled
	 * positive-keys).
	 * </ul>
	 * </quote>
	 * <p>
	 * This method resets the position on the input stream (mark/rewind).
	 */
    private boolean isComment(String starter) {
        int mark = input.mark(); //store position for rewinding
        try {
            match(starter);
            StringBuilder markerBuilder = new StringBuilder();
            while (true) {
                final char point = (char) input.LT(1);
                if (point == '@') { // annotation marker finished
                    if(markerBuilder.length() == 0) {
                        // no markers --> active
                        return false;
                    }
                    String[] markers = markerBuilder.toString().split("(?=[+-])");
                    boolean plusFound = false;
                    boolean plusKeyFound = false;
                    for (int i = 0; i < markers.length; i++) {
                        String marker = markers[i];
                        if (marker.equalsIgnoreCase("-key") ||
                            marker.length() < 2 ||
                            !marker.matches("[+-].+")) {
                               // 1) -key
                               // 2) + or - alone
                               // 3) identifier w/o +/-
                               // means: this is a comment
                            return true;
                        } else if (marker.equalsIgnoreCase("+key")) {
                            plusKeyFound = true;
                        } else if (marker.startsWith("+")) {
                            plusFound = true;
                        }
                    }
                    // it is only a comment if "+" encountered, but not "+key"
                    return plusFound && !plusKeyFound;
                } else if (Character.isJavaIdentifierPart(point) || point == '-' || point == '+') {
                    markerBuilder.append(point);
                    input.consume();
                } else {
                    return true;
                }
            }
        } catch (MismatchedTokenException e) {
            //ignore
        } finally {
            input.rewind(mark);
        }
        return true;
    }

  boolean acceptAt = false;
}

@annotateclass{ @SuppressWarnings("all") } 

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
    ASSIGNS          : 'assigns';
    ASSIGNS_RED      : 'assigns_redundantly';
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
    LOOP_VARIANT     : 'loop_variant';
    LOOP_VARIANT_RED     : 'loop_variant_redundantly';
    DETERMINES                  : 'determines';
    DIVERGES 			: 'diverges';
    DIVERGES_RED 		: 'diverges_redundantly';
    DURATION 			: 'duration';
    DURATION_RED 		: 'duration_redundantly';
    ENSURES 			: 'ensures';
    ENSURES_FREE  : 'ensures_free';
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
    LOOP_CONTRACT  		: 'loop_contract';
    LOOP_INVARIANT  		: 'loop_invariant';
    LOOP_INVARIANT_RED  	: 'loop_invariant_redundantly';
    LOOP_INVARIANT_FREE	: 'loop_invariant_free';
    MAINTAINING  		: 'maintaining';
    MAINTAINING_REDUNDANTLY	: 'maintaining_redundantly';
    MAPS			: 'maps';
    MAPS_RED			: 'maps_redundantly';
    MEASURED_BY                 : 'measured_by';
    MEASURED_BY_REDUNDANTLY     : 'measured_by_redundantly';
    MERGE_POINT         : 'merge_point';
    MERGE_PROC          : 'merge_proc';
    MERGE_PARAMS        : 'merge_params';
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
    READABLE			: 'readable';
    REPRESENTS			: 'represents';
    REPRESENTS_RED		: 'represents_redundantly';
    REQUIRES 			: 'requires';
    REQUIRES_FREE : 'requires_free';
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
    STRICTLY_PURE : 'strictly_pure';
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

ML_COMMENT
:
  {isComment("/*")}? =>
    ('/*' (options { greedy = false; } : .)* '*/')
  { $channel = HIDDEN; }
;

SL_COMMENT
:
  {isComment("//")}? => ('//' ~'\n'*)
  { $channel = HIDDEN; }
;

JML_COMMENT_START
:
  ('//'|'/*') ANNOTATIONS? '@'
  { $channel = HIDDEN; }
;


fragment ANNOTATIONS: ANNOTATION+;
fragment ANNOTATION
:
  ('+'|'-') ('a'..'z'|'A'..'Z')*
  // in early JML //+@ and //-@ was also allowed.
  // we accept both.
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
:
  (
	    ' '
	|   '\t'
	|   '\n'  { acceptAt = true; }
	|   '\r'
	|   {acceptAt}? '@'
	|   ('@*/') => '@*/'
	|   ('*/') => '*/'
  )+
  { $channel = HIDDEN; }
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
    StringBuilder sb = new StringBuilder("{");
}
:
  '{'
  (
    '{'                          { braceCounter++; ignoreAt = false; sb.append("{"); }
  | {braceCounter > 0}? => '}'   { braceCounter--; ignoreAt = false; sb.append("}");}
  | '\n'                         { ignoreAt = true; sb.append("\n"); }
  | '@'                          { sb.append(ignoreAt ? " " : "@"); ignoreAt = false; }
  | c = (' '|'\t'|'\r'|'\u000c') { sb.append((char)c); }
  | c = ~(' '|'\t'|'\r'|'\u000c' | '{' | '}' | '\n' | '@')
                                 { ignoreAt = false; sb.append((char)c); }
  )* 
  {braceCounter == 0}? => '}' 
     { sb.append("}"); setText(sb.toString()); }
;


BRACE_DISPATCH :
   ( '{' ~ '|') => BODY { $type = BODY; }
 | NEST_START { $type = NEST_START; }
 ;

SEMICOLON
:
    ';'
;


//TODO (DS): I wanted two enable the usage of "\old" in STRING_LITERALs for merge params specifications.
//           Therefore, I changed the definition like it can be seen below. Now, however, ANTLR is reporting
//           issues like:
//             Decision can match input such as "'\\''r'" using multiple alternatives: 1, 2
//             As a result, alternative(s) 2 were disabled for that input
//           This probably should be resolved...
STRING_LITERAL
    : '"' ( ESC | ~('"'|'\\') )* '"'
    ;

CHAR_LITERAL:
        '\''
                (~('\''|'\\') |
                 ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | OCT_CHAR))
                 // note: unicode escapes are processed earlier
                )
      '\''
    ;

fragment OCT_CHAR:
        (('0'|'1'|'2'|'3') OCTDIGIT OCTDIGIT) | (OCTDIGIT OCTDIGIT) | OCTDIGIT;

fragment OCTDIGIT: '0'..'7';

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
