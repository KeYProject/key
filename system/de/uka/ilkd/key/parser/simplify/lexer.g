// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/* -*-Antlr-*- */

header {
	package de.uka.ilkd.key.parser.simplify;
}

class SimplifyLexer extends Lexer;

options {
    charVocabulary = '\3'..'\377';  
	k=2;
}

tokens {
    AND = "AND";
    EQ = "EQ";
    NEQ = "NEQ";
//    ARRAY_OP = "ArrayOp";
}

LT : "<";
LEQ : "<=";
PLUS : "+";
MINUS : "-";
MUL : "*";
COLON : ":";
DOT : ".";

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

BAR
options {
  paraphrase = "`|'";
}
	:
	'|' 
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

DIGITS
    :
        (DIGIT)+
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

WS
options {
  paraphrase = "white space";
}
	:	(' '
	|	'\t'
	|	'\n'  { newline(); }
	|	'\r'
        )
		{ $setType(Token.SKIP); }
        
	;
