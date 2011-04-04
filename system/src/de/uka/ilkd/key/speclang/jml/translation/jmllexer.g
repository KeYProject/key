// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
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
 	charVocabulary='\3'..'\ufffe';
 	codeGenMakeSwitchThreshold = 2;  // Some optimizations
	codeGenBitsetTestThreshold = 3;
	k=7;
}

tokens {
    BOOLEAN = "boolean";
    BYTE = "byte";
    FALSE = "false";
    INSTANCEOF = "instanceof";        
    INT = "int";
    LONG = "long";        
    NEW = "new";
    NULL = "null";    
    SHORT = "short";
    SUPER = "super";    
    THIS = "this";
    TRUE = "true";    
    VOID = "void";
}

AND : "&";
ANTIV : "<=!=>";
BIGINT : "\\bigint";
BITWISENOT : "~";
BSUM : "\\bsum";  //KeY extension, not official JML
COLON : ":";
COMMA : ",";
CREATED : "\\created";
CURRENT_MEMORY_AREA : "\\currentMemoryArea"; //KeY extension, not official JML
DIV : "/";
DOT : ".";
DOTDOT : "..";
DURATION : "\\duration";
ELEMTYPE : "\\elemtype";
EQUAL : "==";
EQUAL_SINGLE : "=";
EQV : "<==>";
EVERYTHING : "\\everything";
FRESH : "\\fresh"; 
GEQ : ">=";
GT : ">";
IMPLIES : "==>";
IMPLIESBACKWARD : "<==";
IN_IMMORTAL_MEMORY : "\\inImmortalMemory"; //KeY extension, not official JML
IN_OUTER_SCOPE : "\\inOuterScope"; //KeY extension, not official JML
INCLUSIVEOR : "|";
INTO : "\\into";
INV : "\\inv";
INVARIANT_FOR : "\\invariant_for";
IS_INITIALIZED : "\\is_initialized";
LARROW : "<-";
LBLNEG : "\\lblneg";
LBLPOS : "\\lblpos";
LBRACE : "{";
LEQ : "<=";
LOCKSET : "\\lockset";
LOGICALAND : "&&";
LOGICALOR : "||";
MAX_SPACE : "\\max_space"; //KeY extension, not official JML
MEMORY_AREA : "\\memoryArea"; //KeY extension, not official JML
MINUS : "-";
MOD : "%";
MULT : "*";
NONNULLELEMENTS : "\\nonnullelements";
NON_NULL : "\\non_null";
NULLABLE : "\\nullable";
NOT : "!";
NOT_MODIFIED : "\\not_modified";
NOT_SPECIFIED : "\\not_specified";
NOTEQUAL : "!=";
NOTHING : "\\nothing";
NOWARN : "\\nowarn";
OLD : "\\old";
OTHER : "\\other";
OUTER_SCOPE : "\\outerScope"; //KeY extension, not official JML
PLUS : "+";
PRE : "\\pre";
PRIVATEDATA : "\\private_data";
QUESTIONMARK : "?";
RBRACE : "}";
REACH : "\\reach";
REACHLOCS : "\\reachLocs";
REAL : "\\real";
REENTRANT_SCOPE : "\\reentrantScope"; //KeY extension, not official JML
RESULT : "\\result";
RIGIDWORKINGSPACE : "\\rigid_working_space"; //KeY extension, not official JML
SAME : "\\same";
SEMI : ";";
SHIFTLEFT : "<<";
SHIFTRIGHT : ">>";
SPACE : "\\space";
STRING_EQUAL : "\\string_equal";
TYPEOF : "\\typeof";
TYPE_SMALL : "\\type";
TYPE : "\\TYPE";
ST : "<:";
SUCH_THAT : "\\such_that";
UNSIGNEDSHIFTRIGHT : ">>>";
WORKINGSPACE : "\\working_space";
XOR : "^";

LOCSET : "\\locset";
EMPTYSET : "\\empty";
SINGLETON : "\\singleton";
UNION : "\\set_union";
INTERSECT : "\\intersect";
SETMINUS : "\\set_minus";
ALLFIELDS : "\\all_fields";
UNIONINF: "\\infinite_union";
DISJOINT : "\\disjoint";
SUBSET : "\\subset";
NEWELEMSFRESH : "\\new_elems_fresh";

SEQ : "\\seq";
SEQEMPTY : "\\seq_empty";
SEQSINGLETON : "\\seq_singleton";
SEQCONCAT : "\\seq_concat";
SEQSUB : "\\seq_sub";
SEQREVERSE : "\\seq_reverse";

MEASURED_BY : "\\measured_by";


LT_DISPATCH
     :
     ('<' (LETTER)+ '>') => IMPLICIT_IDENT {$setType(IDENT);}
    |
     LT {$setType(LT);}
    ;
    
protected LT : "<";

    
protected IMPLICIT_IDENT
options {
  paraphrase = "an implicit identifier (letters only)";
}
:
  '<' (LETTER)+ '>'
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
        '\'' 
                ((' '..'&') |
                 ('('..'[') |
                 (']'..'~') |
                 ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"' | 'u' HEXNUMERAL ))
                )
      '\''
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
        |       '\u000C'
        |       '@')
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
