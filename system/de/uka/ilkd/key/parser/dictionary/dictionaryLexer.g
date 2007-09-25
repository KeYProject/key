// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/* -*-Antlr-*- */

header {
   package de.uka.ilkd.key.parser.dictionary;
}

/**
 * The common lexer for declarations, terms, formulae, Taclets, etc.
 */
class DictionaryLexer extends Lexer;

options {
	k=2;
}

protected
VOCAB
   :       '\3'..'\377'
   ;

SEMI
options {
  paraphrase = "`;'";
} :	';'
    ;

SLASH
options {
  paraphrase = "`/'";
} :	'/'
    ;

COLON
    options {
    paraphrase = "`:'";
} :    ':'
    ;

EQUAL
options {
  paraphrase = "`='";
}
	:	'='
	;

COMMA
options {
  paraphrase = "`,'";
}
	:	','
	;

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

LBRACE
options {
  paraphrase = "`{'";
}
	:	'{'
	;

RBRACE
options {
    paraphrase = "`}'";
}
:	'}'
    ;

LBRACKET
options {
    paraphrase = "`['";
}
:	'['
    ;

RBRACKET
options{
    paraphrase = "']'";
}
:	']'
	;


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


/*CARD_LITERAL
options {
    paraphrase = "a non-negative number";
}
    :
    (DIGIT)+
    ;
*/

STRING_LITERAL
options {
  paraphrase = "a string in double quotes";
}
    : '"'! ( ESC | ~('"'|'\\') )* '"'! ;



PRIMES_OR_CHARLITERAL
     :
     ('\'' '\'') => PRIMES {$setType(PRIMES);}
    |
     ('\'' '\\') => CHAR_LITERAL {$setType(CHAR_LITERAL);}
    |
     ('\'' ~('\'') '\'') => CHAR_LITERAL {$setType(CHAR_LITERAL);}
    |
     PRIMES {$setType(PRIMES);}
    ;


protected
PRIMES
options {
  paraphrase = "Sequence of primes (at least one)";
}
	:	('\'')+
	;

protected
CHAR_LITERAL 
options {
  paraphrase = "a char in single quotes";
}
    : '\'' 
                ((' '..'&') |
                 ('('..'[') |
                 (']'..'~') |
                 ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | 'u' HEX ))
                )
      '\''
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
    )
    ;



protected
QUOTED_STRING_LITERAL
options {
  paraphrase = "a string with double quotes";
}
    : '"' ('\\' . | ~('"'|'\\') )* '"' ;



SL_COMMENT
options {
  paraphrase = "a comment";
}

	:
	"//"
	(~'\n')* '\n'
	{ $setType(Token.SKIP); newline(); }
	;


protected
DIGIT
options {
  paraphrase = "a digit";
}
	:	'0'..'9'
	;


protected 
HEX
options {
    paraphrase = "a hexadeciamal number";
}
:	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
	('a'..'f'|'A'..'F'|DIGIT )
    ;

protected
LETTER
options {
    paraphrase = "a letter";
}
:	'a'..'z'|'A'..'Z' 
    ;


protected IDCHAR 
options {
	paraphrase = "an admissible character for identifiers";
}
	: LETTER | DIGIT | '_' | '+' | '~'
	;


IDENT
options {
    testLiterals = true;
    paraphrase = "an identifer";
}

:       ("#" (IDCHAR)*) | IDCHAR (IDCHAR)* | "<" (IDCHAR)* ">"
	;

