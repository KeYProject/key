// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

header {
    package de.uka.ilkd.key.speclang.jml.pretranslation;
}


class KeYJMLPreLexer extends Lexer;


options {
    charVocabulary = '\3'..'\377';
    k=3;
}


tokens {
    ABSTRACT 			= "abstract";
    ALSO 			= "also";
    ASSIGNABLE 			= "assignable";
    ASSIGNABLE_RED 		= "assignable_redundantly";
    BEHAVIOR 			= "behavior";
    BEHAVIOUR 			= "behaviour";
    CAPTURES 			= "captures";
    CAPTURES_RED 		= "captures_redundantly";
    CODE 			= "code";
    CODE_BIGINT_MATH 		= "code_bigint_math";
    CODE_JAVA_MATH 		= "code_java_math";
    CODE_SAFE_MATH		= "code_safe_math";
    CONST 			= "const";
    CONSTRAINT			= "constraint";
    CONSTRAINT_RED		= "constraint_redundantly";
    DECREASES  			= "decreases";
    DECREASES_REDUNDANTLY  	= "decreases_redundantly";
    DECREASING  		= "decreasing";
    DECREASING_REDUNDANTLY  	= "decreasing_redundantly";
    DIVERGES 			= "diverges";
    DIVERGES_RED 		= "diverges_redundantly";
    DURATION 			= "duration";
    DURATION_RED 		= "duration_redundantly";
    ENSURES 			= "ensures";
    ENSURES_RED 		= "ensures_redundantly";
    EXCEPTIONAL_BEHAVIOR 	= "exceptional_behavior";
    EXCEPTIONAL_BEHAVIOUR 	= "exceptional_behaviour";
    FINAL 			= "final";
    FORALL			= "forall";
    GHOST 			= "ghost";
    HELPER 			= "helper";
    IN				= "in";
    IN_RED			= "in_redundantly";
    INITIALLY			= "initially";
    INSTANCE 			= "instance";
    INVARIANT 			= "invariant";
    INVARIANT_RED 		= "invariant_redundantly";
    LOOP_INVARIANT  		= "loop_invariant";
    LOOP_INVARIANT_RED  	= "loop_invariant_redundantly";
    LOOP_PREDICATE 		= "loop_predicate";
    MAINTAINING  		= "maintaining";
    MAINTAINING_REDUNDANTLY	= "maintaining_redundantly";
    MAPS			= "maps";
    MAPS_RED			= "maps_redundantly";	
    MODEL 			= "model";
    MODIFIABLE			= "modifiable";
    MODIFIABLE_RED		= "modifiable_redundantly";
    MODIFIES			= "modifies";
    MODIFIES_RED		= "modifies_redundantly";
    MONITORS_FOR		= "monitors_for";
    NATIVE			= "native";
    NON_NULL 			= "non_null";
    NORMAL_BEHAVIOR 		= "normal_behavior";
    NORMAL_BEHAVIOUR 		= "normal_behaviour";
    NULLABLE 			= "nullable";
    NULLABLE_BY_DEFAULT 	= "nullable_by_default";
    PRIVATE 			= "private";
    PROTECTED 			= "protected";
    PUBLIC			= "public";
    PURE 			= "pure";
    READABLE			= "readable";
    REPRESENTS			= "represents";
    REPRESENTS_RED		= "represents_redundantly";
    REQUIRES 			= "requires";
    REQUIRES_RED 		= "requires_redundantly";
    SET 			= "set";
    SIGNALS 			= "signals";
    SIGNALS_ONLY 		= "signals_only";
    SIGNALS_ONLY_RED 		= "signals_only_redundantly";
    SIGNALS_RED 		= "signals_redundantly";
    SKOLEM_CONSTANT 		= "skolem_constant";
    SPEC_BIGINT_MATH 		= "spec_bigint_math";
    SPEC_JAVA_MATH 		= "spec_java_math";
    SPEC_PROTECTED 		= "spec_protected";
    SPEC_PUBLIC 		= "spec_public";
    SPEC_SAFE_MATH 		= "spec_safe_math";
    STATIC 			= "static";
    STRICTFP 			= "strictfp";
    SYNCHRONIZED 		= "synchronized";
    TRANSIENT 			= "transient";
    UNINITIALIZED 		= "uninitialized";
    VOLATILE 			= "volatile";
    WHEN 			= "when";
    WHEN_RED 			= "when_redundantly";
    WORKING_SPACE 		= "working_space";
    WORKING_SPACE_RED 		= "working_space_redundantly";
    WRITABLE			= "writable";    
}


{
    private boolean expressionMode = false;
    
    public void setExpressionMode(boolean b) {
    	expressionMode = b;
    }
}


protected SL_COMMENT
options {
    paraphrase = "a single-line non-specification comment";
}
:
    "//"
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


protected ML_COMMENT
options {
    paraphrase = "a multi-line non-specification comment";
}
:
    "/*"
    (
        (~('*').|'*'~'/')
        =>
        (	'\n'         { newline(); }
            | 	~('@'|'\n')
        )
    	( 
    	    options { greedy = false; } 
            : 
            	'\n'     { newline(); }
            |	~('\n') 
    	)*
    )? 
    "*/" 
;


WS
options {
    paraphrase = "white space";
}
{
    boolean acceptAt = false;
}
:
    {!expressionMode}?
    ( 
    	    ' '
    	|   '\t'
    	|   '\n'  { newline(); acceptAt = true; }
    	|   '\r'
    	|   {acceptAt}? '@'
    	|   ("//@") => "//@"
    	|   "/*@"
    	|   "@*/"
    	|   "*/"
    	|   SL_COMMENT
    	|   ML_COMMENT
    )+
    { 
    	$setType(Token.SKIP); 
    }
;


protected LETTER
options {
    paraphrase = "letter";
}
:
        'a'..'z'
    |   'A'..'Z'
    |   '_'
    |   '$'
;


protected DIGIT
:	
    '0'..'9'
;


IDENT
options {
    paraphrase = "an identifier";
}
:
    {!expressionMode}?
    LETTER 
    (	options { greedy = true; }
    	:
    	    LETTER 
    	|   DIGIT 
    	|   "[]" 
    	|   '.'
    )*
;


PARAM_LIST
options {
    paraphrase = "a parameter list";
}
:
    {!expressionMode}?
    '(' 
    (IDENT IDENT)?
    (',' IDENT IDENT)* 
    ')'
;   


BODY
options {
    paraphrase = "a method body";
}
{
    int braceCounter = 0;
}
:
    {!expressionMode}?
    '{'
    (
            '{'                      { braceCounter++; }
        |   {braceCounter > 0}? '}'  { braceCounter--; }
        |   '\n'                     { newline(); }
        |   ~'}'
    )* 
    {braceCounter == 0}? '}'
;


INITIALISER
options {
    paraphrase = "an initialiser";
}
:
    {!expressionMode}?
    (
	    ';'
	|   (
	    	'='         { setExpressionMode(true); }
	    	EXPRESSION  { setExpressionMode(false); }
	    )
     )
;


EXPRESSION
{
    int parenthesesCounter = 0;
}
:
    {expressionMode}?
    (
            '('   { parenthesesCounter++; }
        |   ')'   { parenthesesCounter--; }
        |   {parenthesesCounter > 0}? ';'
        |   '\n'  { newline(); }
        |    ~';'
    )* 
    {parenthesesCounter == 0}? ';'
    {
    	expressionMode = false;
    }
;
