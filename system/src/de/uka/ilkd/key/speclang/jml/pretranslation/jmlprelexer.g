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


header {
    package de.uka.ilkd.key.speclang.jml.pretranslation;
}


class KeYJMLPreLexer extends Lexer;


options {
    charVocabulary='\u0003'..'\ufffe';
    codeGenMakeSwitchThreshold = 2;  // Some optimizations
    codeGenBitsetTestThreshold = 3;
    k=2;
}


tokens {
    ABSTRACT 			= "abstract";
    ACCESSIBLE                  = "accessible";
    ACCESSIBLE_REDUNDANTLY      = "accessible_redundantly";
    ALSO 			= "also";
    ASSERT                      = "assert";
    ASSERT_REDUNDANTLY          = "assert_redundantly";
    ASSUME                      = "assume";
    ASSUME_REDUNDANTLY          = "assume_redundantly";
    ASSIGNABLE 			= "assignable";
    ASSIGNABLE_RED 		= "assignable_redundantly";
    AXIOM                       = "axiom";
    BEHAVIOR 			= "behavior";
    BEHAVIOUR 			= "behaviour";
	BREAKS				= "breaks";
	BREAK_BEHAVIOR 	    = "break_behavior";
    BREAK_BEHAVIOUR 	= "break_behaviour";
    CAPTURES 			= "captures";
    CAPTURES_RED 		= "captures_redundantly";
    CODE 			= "code";
    CODE_BIGINT_MATH 		= "code_bigint_math";
    CODE_JAVA_MATH 		= "code_java_math";
    CODE_SAFE_MATH		= "code_safe_math";
    CONST 			= "const";
    CONSTRAINT			= "constraint";
    CONSTRAINT_RED		= "constraint_redundantly";
	CONTINUES			= "continues";
	CONTINUE_BEHAVIOR 	= "continue_behavior";
    CONTINUE_BEHAVIOUR 	= "continue_behaviour";
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
    EXSURES                     = "exsures";
    EXSURES_RED                 = "exsures_redundantly";
    EXTRACT                     = "extract";
    FINAL 			= "final";
    FOR_EXAMPLE			= "for_example";
    FORALL			= "forall";
    GHOST 			= "ghost";
    HELPER 			= "helper";
    IMPLIES_THAT		= "implies_that";
    IN				= "in";
    IN_RED			= "in_redundantly";
    INITIALLY			= "initially";
    INSTANCE 			= "instance";
    INVARIANT 			= "invariant";
    INVARIANT_RED 		= "invariant_redundantly";
    LOOP_INVARIANT  		= "loop_invariant";
    LOOP_INVARIANT_RED  	= "loop_invariant_redundantly";
    MAINTAINING  		= "maintaining";
    MAINTAINING_REDUNDANTLY	= "maintaining_redundantly";
    MAPS			= "maps";
    MAPS_RED			= "maps_redundantly";
    MEASURED_BY                 = "measured_by";
    MEASURED_BY_REDUNDANTLY     = "measured_by_redundantly";
    MODEL 			= "model";
    MODEL_BEHAVIOR 		= "model_behavior";
    MODEL_BEHAVIOUR 		= "model_behaviour";
    MODIFIABLE			= "modifiable";
    MODIFIABLE_RED		= "modifiable_redundantly";
    MODIFIES			= "modifies";
    MODIFIES_RED		= "modifies_redundantly";
    MONITORED                   = "monitored";
    MONITORS_FOR		= "monitors_for";
    NATIVE			= "native";
    NON_NULL 			= "non_null";
    NORMAL_BEHAVIOR 		= "normal_behavior";
    NORMAL_BEHAVIOUR 		= "normal_behaviour";
    NO_STATE			= "no_state";
    NOWARN			= "nowarn";
    NULLABLE 			= "nullable";
    NULLABLE_BY_DEFAULT 	= "nullable_by_default";
    OLD				= "old";
    PRIVATE 			= "private";
    PROTECTED 			= "protected";
    PUBLIC			= "public";
    PURE 			= "pure";
    STRICTLY_PURE               = "strictly_pure";
    READABLE			= "readable";
    REPRESENTS			= "represents";
    REPRESENTS_RED		= "represents_redundantly";
    REQUIRES 			= "requires";
    REQUIRES_RED 		= "requires_redundantly";
	RETURNS				= "returns";
	RETURN_BEHAVIOR 	= "return_behavior";
    RETURN_BEHAVIOUR 	= "return_behaviour";
    SCOPE_SAFE 			= "scopeSafe";
    ARBITRARY_SCOPE             = "arbitraryScope";
    ARBITRARY_SCOPE_THIS        = "arbitraryScopeThis";
    SET 			= "set";
    SIGNALS 			= "signals";
    SIGNALS_ONLY 		= "signals_only";
    SIGNALS_ONLY_RED 		= "signals_only_redundantly";
    SIGNALS_RED 		= "signals_redundantly";
    SPEC_BIGINT_MATH 		= "spec_bigint_math";
    SPEC_JAVA_MATH 		= "spec_java_math";
    SPEC_PROTECTED 		= "spec_protected";
    SPEC_PUBLIC 		= "spec_public";
    SPEC_NAME                   = "name";
    SPEC_SAFE_MATH 		= "spec_safe_math";
    STATIC 			= "static";
    STRICTFP 			= "strictfp";
    SYNCHRONIZED 		= "synchronized";
    TRANSIENT 			= "transient";
    TWO_STATE			= "two_state";
    UNINITIALIZED 		= "uninitialized";
    VOLATILE 			= "volatile";
    WHEN 			= "when";
    WHEN_RED 			= "when_redundantly";
    WORKING_SPACE 		= "working_space";
    WORKING_SPACE_RED 		= "working_space_redundantly";
    WORKING_SPACE_SINGLE_ITERATION	= "working_space_single_iteration";
    WORKING_SPACE_SINGLE_ITERATION_PARAM	= "working_space_single_iteration_param";
    WORKING_SPACE_SINGLE_ITERATION_LOCAL	= "working_space_single_iteration_local";
    WORKING_SPACE_SINGLE_ITERATION_CONSTRUCTED	= "working_space_single_iteration_constructed";
    WORKING_SPACE_SINGLE_ITERATION_REENTRANT	= "working_space_single_iteration_reentrant";
    WORKING_SPACE_CONSTRUCTED 		= "working_space_constructed";
    WORKING_SPACE_LOCAL 		= "working_space_local";
    WORKING_SPACE_CALLER 		= "working_space_caller";
    WORKING_SPACE_REENTRANT 		= "working_space_reentrant";
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
            | 	~'@'
        )
    	(
    	    options { greedy = false; }
            :
            	'\n'     { newline(); }
            |	~'\n'
    	)*
    )?
    "*/"
;


protected PARAM_DECL
options {
    paraphrase = "a parameter declaration";
    ignore = WS;
}
:
    (
    	("non_null" | "nullable")
    	=>
    	{
    	    $append("/*@");
    	}
    	(
		"non_null"
    	    |   "nullable"
    	)
    	{
    	    $append("@*/");
        }
    )?
    IDENT  { $append(" "); }
    IDENT
;



protected LETTER
options {
    paraphrase = "a letter";
}
:
        'a'..'z'
    |   'A'..'Z'
    |   '_'
    |   '$'
    |   '\\'
;


protected DIGIT
options {
    paraphrase = "a digit";
}
:
    '0'..'9'
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
    	|   ("/*@") => "/*@"
    	|   "@*/"
    	|   "*/"
    	|   SL_COMMENT
    	|   ML_COMMENT
    )+
    {
    	$setType(Token.SKIP);
    }
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
    ignore = WS;
}
:
    {!expressionMode}?
    '('
    (
        PARAM_DECL
        (
            ','
            PARAM_DECL
        )*
    )?
    ')'
;


NEST_START
:
    {!expressionMode}?
    "{|"
;

NEST_END
:
    {!expressionMode}?
    "|}"
;


BODY
options {
    paraphrase = "a method body";
}
{
    int braceCounter = 0;
    boolean ignoreAt = false;
}
:
    {!expressionMode}?
    '{'
    (
	   '{'                      { braceCounter++; ignoreAt = false; }
    	|  {braceCounter > 0}? '}'  { braceCounter--; ignoreAt = false; }
    	|  '\n'                     { newline(); ignoreAt = true; }
    	|  ' '
    	|  '\u000C'
    	|  '\t'
    	|  '\r'
    	|  {!ignoreAt}? '@'
    	|  {ignoreAt}? '@'!	    { ignoreAt = false; }
    	|  ~'}'			    { ignoreAt = false; }
    )*
    {braceCounter == 0}? '}'
;


INITIALISER
options {
    paraphrase = "an initialiser";
}
{
    assert inputState.guessing == 0;
}
:
    {!expressionMode}?
    (
	'='         { setExpressionMode(true); }
	EXPRESSION  { setExpressionMode(false); }
    )
;


SEMICOLON
options {
    paraphrase = "a semicolon";
}
:
    {!expressionMode}?
    ';'
;

STRING_LITERAL
options {
  paraphrase = "a string in double quotes";
}
    : '"'! ( ESC | ~('"'|'\\') )* '"'!
    ;

protected
ESC
    :	'\\'
    (	'n'         { $setText("\n"); }
	|	'r' { $setText("\r"); }
	|	't' { $setText("\t"); }
	|	'b' { $setText("\b"); }
	|	'f' { $setText("\f"); }
	|	'"' { $setText("\""); }
	|	'\'' { $setText("'"); }
	|	'\\' { $setText("\\"); }
	|	':' { $setText ("\\:"); }
	|	' ' { $setText ("\\ "); }
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
;


    AXIOM_NAME_BEGIN
    options {
      paraphrase = "`['";
    }
        :
        '['
        ;

    AXIOM_NAME_END
    options {
      paraphrase = "`]'";
    }
        :
        ']'
        ;

