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
    DECREASES       = "decreases";
    DEPENDS         = "depends";
    DETERMINES      = "determines";
    ENSURES         = "ensures";
    LOOP_DETERMINES = "loop_determines";
    LOOP_SEPARATES  = "loop_separates";
    MODEL_METHOD_AXIOM    = "model_method_axiom";
    NON_NULL        = "non_null";
    NULLABLE        = "nullable";
    REPRESENTS      = "represents";
    REQUIRES        = "requires";
    RETURNS         = "returns";
    SECURE_FOR      = "secure_for";
    SEPARATES       = "separates";
    SIGNALS         = "signals";
    SIGNALS_ONLY    = "signals_only";

    /* JML keywords prefixed with a backslash */
    ALLFIELDS            = "\\all_fields";
    ALLOBJECTS           = "\\all_objects";
    BACKUP               = "\\backup";
    BIGINT               = "\\bigint";
    BSUM                 = "\\bsum";  //KeY extension, not official JML
    BY                   = "\\by";
    CREATED              = "\\created";
    CURRENT_MEMORY_AREA  = "\\currentMemoryArea"; //KeY extension, not official JML
    DECLASSIFIES         = "\\declassifies";
    DISJOINT             = "\\disjoint";
    DOMAIN_IMPLIES_CREATED = "\\domain_implies_created";
    DURATION             = "\\duration";
    ELEMTYPE             = "\\elemtype";
    EMPTYSET             = "\\empty";
    ERASES               = "\\erases";
    EVERYTHING           = "\\everything";
    EXISTS               = "\\exists";
    FORALL               = "\\forall";
    FREE                 = "\\free";
    FRESH                = "\\fresh";
    INDEX                = "\\index";
    INDEXOF              = "\\seq_indexOf";
    INTERSECT            = "\\intersect";
    INTO                 = "\\into";
    INV                  = "\\inv";
    INVARIANT_FOR        = "\\invariant_for";
    IN_DOMAIN            = "\\in_domain";
    IN_IMMORTAL_MEMORY   = "\\inImmortalMemory"; //KeY extension, not official JML
    IN_OUTER_SCOPE       = "\\inOuterScope"; //KeY extension, not official JML
    IS_FINITE            = "\\is_finite";
    IS_INITIALIZED       = "\\is_initialized";
    ITSELF               = "\\itself";
    LBLNEG               = "\\lblneg";
    LBLPOS               = "\\lblpos";
    LESS_THAN_NOTHING    = "\\less_than_nothing";   //KeY extension for strict purity, not official JML (MU); 
                // less_than_nothing is *deprecated* and to be removed eventually, use strictly_nothing instead
    LOCKSET              = "\\lockset";
    LOCSET               = "\\locset";
    MAP                  = "\\map";
    MAPEMPTY             = "\\map_empty";
    MAP_GET              = "\\map_get";
    MAP_OVERRIDE         = "\\map_override";
    MAP_REMOVE           = "\\map_remove";
    MAP_SINGLETON        = "\\map_singleton";
    MAP_SIZE             = "\\map_size";
    MAP_UPDATE           =  "\\map_update";
    MAX                  = "\\max";
    MAX_SPACE            = "\\max_space"; //KeY extension, not official JML
    MEASURED_BY          = "\\measured_by";
    MEMORY_AREA          = "\\memoryArea"; //KeY extension, not official JML
    MIN                  = "\\min";
    NEWELEMSFRESH        = "\\new_elems_fresh";
    NEW_OBJECTS          = "\\new_objects";
    NONNULLELEMENTS      = "\\nonnullelements";
    NOTHING              = "\\nothing";
    NOT_ASSIGNED         = "\\not_assigned";
    NOT_MODIFIED         = "\\not_modified";
    NOT_SPECIFIED        = "\\not_specified";
    NUM_OF               = "\\num_of";
    OLD                  = "\\old";
    OTHER                = "\\other";
    OUTER_SCOPE          = "\\outerScope"; //KeY extension, not official JML
    PRE                  = "\\pre";
    PRIVATEDATA          = "\\private_data";
    PRODUCT              = "\\product";
    REACH                = "\\reach";
    REACHLOCS            = "\\reachLocs";
    REAL                 = "\\real";
    REENTRANT_SCOPE      = "\\reentrantScope"; //KeY extension, not official JML
    RESULT               = "\\result";
    RIGIDWORKINGSPACE    = "\\rigid_working_space"; //KeY extension, not official JML
    SAME                 = "\\same";
    SEQ                  = "\\seq";
    SEQ2MAP              = "\\seq_2_map";
    SEQCONCAT            = "\\seq_concat";
    SEQDEF               = "\\seq_def";
    SEQEMPTY             = "\\seq_empty";
    SEQGET               = "\\seq_get";
    SEQREPLACE           = "\\seq_put";
    SEQREVERSE           = "\\seq_reverse";
    SEQSINGLETON         = "\\seq_singleton";
    SEQSUB               = "\\seq_sub";
    SETMINUS             = "\\set_minus";
    SINGLETON            = "\\singleton";
    SPACE                = "\\space";
    STATIC_INVARIANT_FOR = "\\static_invariant_for";
    STRICTLY_NOTHING     = "\\strictly_nothing";
    STRING_EQUAL         = "\\string_equal";
    SUBSET               = "\\subset";
    SUCH_THAT            = "\\such_that";
    SUM                  = "\\sum";
    TRANSACTIONUPDATED   = "\\transactionUpdated";
    TRANSIENT            = "\\transient";
    TYPE                 = "\\TYPE";
    TYPEOF               = "\\typeof";
    TYPE_SMALL           = "\\type";
    UNION                = "\\set_union";
    UNIONINF             = "\\infinite_union";
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
      LT (LETTER)+ GT {$setType(IDENT);}
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
