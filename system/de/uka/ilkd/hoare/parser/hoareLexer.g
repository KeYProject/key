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
    package de.uka.ilkd.hoare.parser;
    import java.io.InputStream;
    import java.util.HashMap;
    import antlr.TokenStreamSelector;
    import java.util.NoSuchElementException;
    import java.io.*;
}

/**
 * The lexer for Hoare programs
 */

class KeYHoareLexer extends Lexer;
options {
    k=2;
    defaultErrorHandler = false;
}

tokens {
        // Those guys can stay being keywords
    IF = "if";
    ELSE = "else";
    WHILE = "while";
    TRUE = "true";
    FALSE = "false";
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

COLON
    options {
    paraphrase = "`:'";
} :    ':'
    ;

ASSIGN
    options {
    paraphrase = "`='";
} :    "="
    ;

DOT
options {
  paraphrase = "`.'";
}
	:	'.'
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

OR
options {
  paraphrase = "`|'";
}
	:	'|'
	;

AND
options {
  paraphrase = "`&'";
}
	:	'&'
	;

NOT
options {
  paraphrase = "`!'";
}
	:	'!'
	;

EQUALS
options {
  paraphrase = "`=='";
}
	:	"=="
	;


MOD 
options {
  paraphrase = "`%'";
}
      :   '%'
      ;

DIV
options {
  paraphrase = "`/'";
} :	'/'
    ;

MULT
options {
  paraphrase = "`*'";
}
      :   '*'
      ;

MINUS
options {
  paraphrase = "`-'";
}
      :   '-'
      ;

PLUS
options {
  paraphrase = "`+'";
}
      :   '+'
      ;

GT
options {
  paraphrase = "`>'";
}
      :   '>'
      ;

GEQ
options {
  paraphrase = "`>='";
}
      :   '>' '='
      ;


WS
options {
  paraphrase = "white space";
}
      :       (' '
      |       '\t'
      |       '\n'  { newline(); }
      |       '\r'  {if(LA(1) != '\n') newline();} )
	      { $setType(Token.SKIP); }
      ;

STRING_LITERAL
options {
  paraphrase = "a string in double quotes";
}
    : '"' ( ESC | '\n' { newline(); } |~('\n' | '"' | '\\' | '\uFFFF') )* '"' ;


LT
options {
  paraphrase = "'<'";
}
:
  '<'
;

LEQ
options {
  paraphrase = "'<='";
}
:
  '<' '='
;

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
	|	':' { $setText ("\\:"); }
	|	' ' { $setText ("\\ "); }
    )
    ;

protected
QUOTED_STRING_LITERAL
options {
  paraphrase = "a string with double quotes";
}
    : '"' ('\\' . | '\n' {newline();} | ~('\n' | '"' | '\\') )* '"' ;
    
SL_COMMENT
options {
  paraphrase = "a comment";
}

	:
	"//"
	(~('\n' | '\uFFFF'))* ('\n' | '\uFFFF')
	{ $setType(Token.SKIP); newline(); }
	;

ML_COMMENT
options {
  paraphrase = "a comment";
}
	:
	"/*" {
	  while(true) {
	    if((LA(1) == '\r' && LA(2) != '\n') ||
		LA(1) == '\n') newline();
	    if(LA(1) == '*' && LA(2) == '/') {
	      match("*/");
	      break;
	    }
	    matchNot(EOF_CHAR);
	  }
	  $setType(Token.SKIP);
	}
	;

// A single Digit that is followed by a ( is an ident, otherwise it's a number

DIGIT_DISPATCH
:
  ('0' 'x') => HEX_LITERAL {$setType(NUM_LITERAL);}
  | NUM_LITERAL {$setType(NUM_LITERAL);}
;

protected
HEX_LITERAL
options {
  paraphrase = "a hexadeciaml constant";
}
	: '0' 'x' (DIGIT | 'a'..'f' | 'A'..'F')+
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
	: LETTER | DIGIT | '_' | '#'
	;

IDENT
options {
    testLiterals = true;
    paraphrase = "an identifer";
}

:  ('$')? (LETTER | '_' | '#') (IDCHAR)* 
;

protected
NUM_LITERAL
options {
    paraphrase = "a number";
}
    : 
    (DIGIT)+    
    ;

