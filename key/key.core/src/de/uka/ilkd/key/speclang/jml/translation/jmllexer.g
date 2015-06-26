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

    /* Java keywords */
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

    /* JML and JML* keywords */
    ACCESSIBLE      = "accessible";
    ASSIGNABLE      = "assignable";
    BREAKS          = "breaks";
    CONTINUES       = "continues";
    DECREASES       = "decreases"; // internal translation for 'measured_by'
    DEPENDS         = "depends";  // internal translation for 'accessible' on model fields
    DETERMINES      = "determines";  //KeY extension, not official JML
    ENSURES         = "ensures";
    ENSURES_FREE    = "ensures_free";
    LOOP_DETERMINES = "loop_determines";  // internal translation for 'determines' in loop invariants
    LOOP_SEPARATES  = "loop_separates";  //KeY extension, deprecated
    MODEL_METHOD_AXIOM    = "model_method_axiom";  //KeY extension, not official JML
    NON_NULL        = "non_null";
    NULLABLE        = "nullable";
    REPRESENTS      = "represents";
    REQUIRES        = "requires";
    REQUIRES_FREE   = "requires_free";
    RETURNS         = "returns";  //KeY extension, not official JML
    JOIN_PROC       = "join_proc";  //KeY extension, not official JML
    SEPARATES       = "separates";  //KeY extension, not official JML
    SIGNALS         = "signals";
    SIGNALS_ONLY    = "signals_only";

    /* JML keywords prefixed with a backslash */
    ALLFIELDS            = "\\all_fields";  //KeY extension, not official JML
    ALLOBJECTS           = "\\all_objects";  //KeY extension, not official JML
    BACKUP               = "\\backup";  //KeY extension, not official JML
    BIGINT               = "\\bigint";
    BSUM                 = "\\bsum";  //KeY extension, not official JML
    BY                   = "\\by";  //KeY extension, not official JML
    DECLASSIFIES         = "\\declassifies";  //KeY extension, not official JML
    DISJOINT             = "\\disjoint";  //KeY extension, not official JML
    DOMAIN_IMPLIES_CREATED = "\\domain_implies_created";  //KeY extension, not official JML
    DURATION             = "\\duration";
    ELEMTYPE             = "\\elemtype";
    EMPTYSET             = "\\empty";
    ERASES               = "\\erases";  //KeY extension, not official JML
    EVERYTHING           = "\\everything";
    EXISTS               = "\\exists";
    FORALL               = "\\forall";
    FREE                 = "\\free";  //KeY extension, not official JML
    FRESH                = "\\fresh";
    INDEX                = "\\index";
    INDEXOF              = "\\seq_indexOf";  //KeY extension, not official JML
    INTERSECT            = "\\intersect";  //KeY extension, not official JML
    INTO                 = "\\into";
    INV                  = "\\inv";  //KeY extension, not official JML
    INVARIANT_FOR        = "\\invariant_for";
    IN_DOMAIN            = "\\in_domain";  //KeY extension, not official JML
    IS_FINITE            = "\\is_finite";  //KeY extension, not official JML
    IS_INITIALIZED       = "\\is_initialized";
    ITSELF               = "\\itself";  //KeY extension, not official JML
    LBLNEG               = "\\lblneg";
    LBLPOS               = "\\lblpos";
    LOCKSET              = "\\lockset";
    LOCSET               = "\\locset";  //KeY extension, not official JML
    MAP                  = "\\map";  //KeY extension, not official JML
    MAPEMPTY             = "\\map_empty";  //KeY extension, not official JML
    MAP_GET              = "\\map_get";  //KeY extension, not official JML
    MAP_OVERRIDE         = "\\map_override";  //KeY extension, not official JML
    MAP_REMOVE           = "\\map_remove";  //KeY extension, not official JML
    MAP_SINGLETON        = "\\map_singleton";  //KeY extension, not official JML
    MAP_SIZE             = "\\map_size";  //KeY extension, not official JML
    MAP_UPDATE           =  "\\map_update";  //KeY extension, not official JML
    MAX                  = "\\max";
    MEASURED_BY          = "\\measured_by";
    MIN                  = "\\min";
    NEWELEMSFRESH        = "\\new_elems_fresh";  //KeY extension, not official JML
    NEW_OBJECTS          = "\\new_objects";  //KeY extension, not official JML
    NONNULLELEMENTS      = "\\nonnullelements";
    NOTHING              = "\\nothing";
    NOT_ASSIGNED         = "\\not_assigned";
    NOT_MODIFIED         = "\\not_modified";
    NOT_SPECIFIED        = "\\not_specified";
    NUM_OF               = "\\num_of";
    OLD                  = "\\old";
    PERMISSION           = "\\permission";
    PRE                  = "\\pre";
    PRODUCT              = "\\product";
    REACH                = "\\reach";
    REACHLOCS            = "\\reachLocs";  //KeY extension, not official JML
    REAL                 = "\\real";
    RESULT               = "\\result";
    SAME                 = "\\same";
    SEQ                  = "\\seq";  //KeY extension, not official JML
    SEQ2MAP              = "\\seq_2_map";  //KeY extension, not official JML
    SEQCONCAT            = "\\seq_concat";  //KeY extension, not official JML
    SEQDEF               = "\\seq_def";  //KeY extension, not official JML
    SEQEMPTY             = "\\seq_empty";  //KeY extension, not official JML
    SEQGET               = "\\seq_get";  //KeY extension, not official JML
    SEQREPLACE           = "\\seq_put";  //KeY extension, not official JML
    SEQREVERSE           = "\\seq_reverse";  //KeY extension, not official JML
    SEQSINGLETON         = "\\seq_singleton";  //KeY extension, not official JML
    SEQSUB               = "\\seq_sub";  //KeY extension, not official JML
    SETMINUS             = "\\set_minus";  //KeY extension, not official JML
    SINGLETON            = "\\singleton";  //KeY extension, not official JML
    SPACE                = "\\space";
    STATIC_INVARIANT_FOR = "\\static_invariant_for";  //KeY extension, not official JML
    STRICTLY_NOTHING     = "\\strictly_nothing";  //KeY extension, not official JML
    STRING_EQUAL         = "\\string_equal";  //KeY extension, not official JML
    SUBSET               = "\\subset";
    SUCH_THAT            = "\\such_that";
    SUM                  = "\\sum";
    TRANSACTIONUPDATED   = "\\transactionUpdated";  //KeY extension, not official JML
    TRANSIENT            = "\\transient";  //KeY extension, not official JML
    TYPE                 = "\\TYPE";
    TYPEOF               = "\\typeof";
    TYPE_SMALL           = "\\type";
    UNION                = "\\set_union";  //KeY extension, not official JML
    UNIONINF             = "\\infinite_union";  //KeY extension, not official JML
    VALUES               = "\\values";
    WORKINGSPACE         = "\\working_space";
    // ONLY_ACCESSED     = "\\only_accessed"; // too many common lexemes
    // ONLY_ASSIGNED     = "\\only_assigned";
    // ONLY_CALLED       = "\\only_called";
    // ONLY_CAPTURED     = "\\only_captured";
}


AND : "&";
BITWISENOT : "~";
COLON : ":";
COMMA : ",";
DIV : "/";
DOT : ".";
DOTDOT : "..";
EQUAL_SINGLE : "=";
EQV_ANTIV: "<==>" | "<=!=>";
EQ_NEQ : "==" | "!=";
GEQ : ">=";
IMPLIES : "==>";
IMPLIESBACKWARD : "<==";
INCLUSIVEOR : "|";
LARROW : "<-";
LBRACE : "{";
LEQ : "<=";
LOCKSET_LEQ: "<#=";
LOCKSET_LT: "<#";
LOGICALAND : "&&";
LOGICALOR : "||";
MINUS : "-";
MOD : "%";
MULT : "*";
NOT : "!";
PLUS : "+";
QUESTIONMARK : "?";
RBRACE : "}";
SEMI : ";";
SHIFTLEFT : "<<";
SHIFTRIGHT : ">>";
ST : "<:";
UNSIGNEDSHIFTRIGHT : ">>>";
XOR : "^";


protected GT : ">";
protected LT : "<";

protected IMPLICIT_IDENT
options {
  paraphrase = "an implicit identifier (letters only)";
}
:
  LT (LETTER)+ GT
;

LT_IMPLICIT_GT_DISPATCH
    :
      (LT (LETTER)+ GT) => LT (LETTER)+ GT {$setType(IDENT);}
    |
      LT {$setType(LT);}
    |
      GT {$setType(GT);}
    
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

protected
JML_IDENT 
options {
    testLiterals = true;
    paraphrase = "JML identifier prefixed with \\";
}:
  "\\" IDENT ;

protected
DL_ESCAPE 
options {
    paraphrase = "Escaped JavaDL identifier";
}:
  "\\dl_"  LETTER  ( LETTERORDIGIT )*  ;

BACKSLASH_PREFIXED:
   ("\\dl_") => DL_ESCAPE { $setType(DL_ESCAPE); }
 | ("\\nowarn") => PRAGMA { $setType(PRAGMA); }
 | JML_IDENT
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
//	| PRAGMA (~';')* SEMI
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
