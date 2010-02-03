// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
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
	package de.uka.ilkd.key.speclang.ocl.translation;
}

class KeYOCLLexer extends Lexer;

options {
  testLiterals=true;
  k = 2;
}

tokens {
    FALSE   = "false";
    TRUE    = "true";
    NULL    = "null";
    AND     = "and";
    OR      = "or";
    NOT     = "not";
    XOR     = "xor";
    IMPLIES = "implies";
    IF      = "if";
    THEN    = "then";
    ELSE    = "else";
    ENDIF   = "endif";
    PRE     = "pre";
    SET     = "Set";
    BAG     = "Bag";
    SEQUENCE = "Sequence";
    COLLECTION = "Collection";
}

LPAREN	: "(";
RPAREN	: ")";
LBRACK	: "[";
RBRACK	: "]";
LCURLY	: "{";
RCURLY	: "}";
COLON	: ":";
DCOLON	: "::";
COMMA	: ",";
EQUAL	: "=";
NEQUAL	: "<>";
LT	: "<";
GT	: ">";
LE	: "<=";
GE	: ">=";
RARROW	: "->";
DOTDOT	: "..";
DOT	: ".";
POUND	: "#";
SEMICOL	: ";";
BAR	: "|";
ATSIGN	: "@";
PLUS	: "+";
MINUS	: "-";
MULT	: "*";
DIVIDE	: "/";

WS	
options {
  paraphrase = "white space";
}
	:	(' '
	|	'\t'
	|	'\n'  { newline(); }
	|	'\r')
		{ $setType(Token.SKIP); }
	;

NAME 
options {
  testLiterals = true;
}
    : ( ('a'..'z') | ('A'..'Z') | ('_') ) 
        ( ('a'..'z') | ('0'..'9') | ('A'..'Z') | ('_') )* 
  ;

NUMBER 
  : ('0'..'9')+
//    ( { LA(2) != '.' }? '.' ('0'..'9')+ )?
//    ( ('e' | 'E') ('+' | '-')? ('0'..'9')+ )?
  ;

STRING : '\'' ( ( ~ ('\'' | '\\' | '\n' | '\r') )
	| ('\\' ( ( 'n' | 't' | 'b' | 'r' | 'f' | '\\' | '\'' | '\"' )
		| ('0'..'3')
		  (
			options {
			  warnWhenFollowAmbig = false;
			}
		  :	('0'..'7')
			(	
			  options {
				warnWhenFollowAmbig = false;
			  }
			:	'0'..'7'
			)?
		  )?
		|	('4'..'7')
		  (
			options {
			  warnWhenFollowAmbig = false;
			}
		  :	('0'..'9')
		  )? ) ) )* '\''
    ;

SL_COMMENT: "--" (~'\n')* '\n' {$setType(Token.SKIP); newline();}
        ;
