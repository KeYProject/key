// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

/* -*-Antlr-*- */

header {
	package de.uka.ilkd.key.speclang.jml.translation;
}

class KeYJMLLexer extends Lexer;

options {
    charVocabulary = '\3'..'\377';  
	k=7;
}

tokens {
    SET = "set";
    NEW = "new";
    BYTE = "byte";
    SHORT = "short";
    INT = "int";
    LONG = "long";
    BOOLEAN = "boolean";
    AT = "@";
    PLUS = "+";
    MINUS = "-";
    IMPLIES = "==>";
    IMPLIESBACKWARD = "<==";
    LOGICALOR = "||";
    LOGICALAND = "&&";
    INCLUSIVEOR = "|";
    XOR = "^";
    AND = "&";
    EQUAL = "==";
    NOTEQUAL = "!=";
    ALSO = "also";
//    MULT = "*";
//    DIV = "/";
    MOD = "%";
    TRUE = "true";
    FALSE = "false";
    EQV = "<==>";
    ANTIV = "<=!=>";
    NOT = "!";
    BITWISENOT = "~";
    SEMI = ";";
    COMMA = ",";
    LPAREN = "(";
    RPAREN = ")";
    LBRACKET = "[";
    RBRACKET = "]";
    SHIFTRIGHT = ">>";
    SHIFTLEFT = "<<";
    UNSIGNEDSHIFTRIGHT = ">>>";
    NULL = "null";
    IF = "if";
    INSTANCEOF = "instanceof";
    COLON = ":";
    QUESTIONMARK = "?";
    THIS = "this";
    SUPER = "super";
    MODEL = "model";
    RETURNS = "returns";
    UNINITIALIZED = "uninitialized";
    SPEC_JAVA_MATH = "spec_java_math";
    SPEC_SAVE_MATH = "spec_safe_math";
    SPEC_BIGINT_MATH = "spec_bigint_math";
    CODE_JAVA_MATH = "code_java_math"; 
    CODE_SAFE_MATH = "code_safe_math"; 
    CODE_BIGINT_MATH = "code_bigint_math";
    CODE_CONTRACT = "code_contract";
}

LARROW : "<-";
NOT : "!";
BITWISENOT : "~";
LT : "<";
GT : ">";
LEQ : "<=";
GEQ : ">=";
ST : "<:";
PLUS : "+";
MINUS : "-";
IMPLIES : "==>";
IMPLIESBACKWARD : "<==";
LOGICALOR : "||";
LOGICALAND : "&&";
INCLUSIVEOR : "|";
SHIFTRIGHT : ">>";
SHIFTLEFT : "<<";
UNSIGNEDSHIFTRIGHT : ">>>";
XOR : "^";
AND : "&";
EQUAL : "==";
NOTEQUAL : "!=";
MULT : "*";
DIV : "/";
MOD : "%";
EQV : "<==>";
ANTIV : "<=!=>";
SEMI : ";";
SUCH_THAT : "\\such_that";
NOT_SPECIFIED : "\\not_specified";
RESULT : "\\result";
NOTHING : "\\nothing";
EVERYTHING : "\\everything"; 
PRIVATEDATA : "\\private_data";
OBJECT_CREATION: "\\object_creation"; //KeY extension, not official JML
INTO : "\\into";
OLD : "\\old";
PRE : "\\pre";
CREATED : "\\created";
BIGINT : "\\bigint";
COMMA : ",";
DOT : ".";
DOTDOT : "..";
COLON : ":";
QUESTIONMARK : "?";
NOT_MODIFIED : "\\not_modified";
NONNULLELEMENTS : "\\nonnullelements";
OTHER : "\\other";
LBRACE : "{";
RBRACE : "}";

FRESH : "\\fresh";
REACH : "\\reach";
REAL : "\\real";
DURATION : "\\duration";
SPACE : "\\space";
WORKINGSPACE : "\\working_space";
RIGIDWORKINGSPACE : "\\rigid_working_space"; //KeY extension, not official JML
TYPEOF : "\\typeof";
ELEMTYPE : "\\elemtype";
TYPE_SMALL : "\\type";
LOCKSET : "\\lockset";
IS_INITIALIZED : "\\is_initialized";
INVARIANT_FOR : "\\invariant_for";
LBLNEG : "\\lblneg";
LBLPOS : "\\lblpos";
TYPE : "\\TYPE";
NOWARN : "\\nowarn";
CURRENT_MEMORY_AREA : "\\currentMemoryArea"; //KeY extension, not official JML
IN_IMMORTAL_MEMORY : "\\inImmortalMemory"; //KeY extension, not official JML
OUTER_SCOPE : "\\outerScope"; //KeY extension, not official JML
IN_OUTER_SCOPE : "\\inOuterScope"; //KeY extension, not official JML


LPAREN
options {
  paraphrase = "`('";
}
	:
	'(' 
	;

RPAREN
options {
    paraphrase = "`)'";
}
:	')'
    ;

LBRACKET
options {
  paraphrase = "`['";
}
	:
	'[' 
	;

RBRACKET
options {
  paraphrase = "`]'";
}
	:
	']' 
	;

QUANTIFIER 
    :
        "\\forall" 
    |
        "\\exists"
    |
        "\\min"
    |
        "\\max"
    | 
        "\\num_of"
    |
        "\\product"
    |
        "\\sum"
    ;

protected
LETTER
options {
    paraphrase = "a letter";
}
    :
        'a'..'z'
    |
        'A'..'Z'
    |
        '_'
    |
        '$'
;

protected
DIGIT
options {
  paraphrase = "a digit";
}
	:	
        '0'..'9'
;

protected
HEXDIGIT
options {
  paraphrase = "a hexadecimal digit";
}
    :
        DIGIT | 'a' .. 'f'
              | 'A' .. 'F'
;

protected
LETTERORDIGIT
    :
        LETTER | DIGIT
;

IDENT
options {
    testLiterals = true;
    paraphrase = "an identifier";
}:
        LETTER (LETTERORDIGIT)*
;

HEXNUMERAL
    :
        '0'! ('x'!|'X'!) (HEXDIGIT)+
;

DIGITS
    :
        (DIGIT)+
;

CHAR_LITERAL:
        '\'' //not completed
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

WS
options {
  paraphrase = "white space";
}
	:	(' '
	|	'\t'
	|	'\n'  { newline(); }
	|	'\r'
    |   '@')
		{ $setType(Token.SKIP); }
	;


INFORMAL_DESCRIPTION
options {
  paraphrase = "informal specification";
}
    : 
        "(*" 
        (
            '*' ~')'
        |	
            ~'*'
        )*
        "*)"
    ;

SL_COMMENT
options {
  paraphrase = "comment";
}

	:
	"//"
	(~'\n')* '\n'
	{ $setType(Token.SKIP); newline(); }
	;

DOC_COMMENT
options {
  paraphrase = "comment";
}
	:
	"/**"
	(
	        '\n' { newline(); }
	 |	'*' ~'/'
	 |	~'*'
	)*
	"*/"
	{ $setType(Token.SKIP);  }
	;
