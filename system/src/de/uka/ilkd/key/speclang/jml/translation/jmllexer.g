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

    ACCESSIBLE      = "accessible";
    ASSIGNABLE      = "assignable";
    ENSURES         = "ensures";
    DECLASSIFY      = "declassify";
    DEPENDS         = "depends";
    MODEL_METHOD_AXIOM    = "model_method_axiom";
    REPRESENTS      = "represents";
    REQUIRES        = "requires";
    RESPECTS        = "respects";
    SECURE_FOR      = "secure_for";
    SIGNALS         = "signals";
    SIGNALS_ONLY    = "signals_only";

    NULLABLE        = "nullable";
    NON_NULL        = "non_null";

    BREAKS          = "breaks";
    CONTINUES       = "continues";
    RETURNS         = "returns";
}

AND : "&";
BACKUP : "\\backup";
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
EQUAL_SINGLE : "=";
EVERYTHING : "\\everything";
FRESH : "\\fresh";
FREE : "\\free";
GEQ : ">=";
GT : ">";
IMPLIES : "==>";
IMPLIESBACKWARD : "<==";
IN_IMMORTAL_MEMORY : "\\inImmortalMemory"; //KeY extension, not official JML
IN_OUTER_SCOPE : "\\inOuterScope"; //KeY extension, not official JML
INCLUSIVEOR : "|";
INDEX : "\\index";
INTO : "\\into";
INV : "\\inv";
INVARIANT_FOR : "\\invariant_for";
IS_INITIALIZED : "\\is_initialized";
LARROW : "<-";
LBLNEG : "\\lblneg";
LBLPOS : "\\lblpos";
LBRACE : "{";
LEQ : "<=";
LESS_THAN_NOTHING : "\\less_than_nothing";   //KeY extension for strict purity, not official JML (MU);
// less_than_nothing is *deprecated* and to be removed eventually, use strictly_nothing instead
LOCKSET : "\\lockset";
LOCKSET_LT: "<#";
LOCKSET_LEQ: "<#=";
LOGICALAND : "&&";
LOGICALOR : "||";
MAX_SPACE : "\\max_space"; //KeY extension, not official JML
MEASURED_BY : "\\measured_by";
MEMORY_AREA : "\\memoryArea"; //KeY extension, not official JML
MINUS : "-";
MOD : "%";
MULT : "*";
NONNULLELEMENTS : "\\nonnullelements";
NOT : "!";
NOT_ASSIGNED: "\\not_assigned";
NOT_MODIFIED : "\\not_modified";
NOT_SPECIFIED : "\\not_specified";
NOTHING : "\\nothing";
OLD : "\\old";
// ONLY_ACCESSED: "\\only_accessed"; // too many common lexemes
// ONLY_ASSIGNED: "\\only_assigned";
// ONLY_CALLED: "\\only_called";
// ONLY_CAPTURED: "\\only_captured";
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
STRICTLY_NOTHING : "\\strictly_nothing";
STRING_EQUAL : "\\string_equal";
TRANSACTIONUPDATED: "\\transactionUpdated";
TYPEOF : "\\typeof";
TYPE_SMALL : "\\type";
TYPE : "\\TYPE";
ST : "<:";
SUCH_THAT : "\\such_that";
UNSIGNEDSHIFTRIGHT : ">>>";
VALUES : "\\values";
WORKINGSPACE : "\\working_space";
XOR : "^";

LOCSET : "\\locset";
EMPTYSET : "\\empty";
SINGLETON : "\\singleton";
UNION : "\\set_union";
INTERSECT : "\\intersect";
SETMINUS : "\\set_minus";
ALLFIELDS : "\\all_fields";
ALLOBJECTS : "\\all_objects";
UNIONINF: "\\infinite_union";
DISJOINT : "\\disjoint";
SUBSET : "\\subset";
NEWELEMSFRESH : "\\new_elems_fresh";

SEQ : "\\seq";
SEQGET : "\\seq_get";
SEQEMPTY : "\\seq_empty";
SEQSINGLETON : "\\seq_singleton";
SEQCONCAT : "\\seq_concat";
SEQSUB : "\\seq_sub";
SEQREVERSE : "\\seq_reverse";
SEQREPLACE : "\\seq_put";
INDEXOF : "\\indexOf";
SEQDEF : "\\seq_def";


FROM : "\\from";
TO : "\\to";
IF : "\\if";

DL_ESCAPE : "\\dl_"  LETTER  ( LETTERORDIGIT )*  ;

EQV_ANTIV: "<==>" | "<=!=>";
EQ_NEQ : "==" | "!=";


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
	| PRAGMA (~';')* SEMI
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


	protected PRAGMA
	    options {
	        paraphrase = "lexical pragma (see Sect. 4.2 of JML reference)";
	    }
	    :
	    "\\nowarn"
	;
