// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

header {
    package de.uka.ilkd.asmkey.parser.antlr;

    import java.io.*;
    import de.uka.ilkd.key.parser.ParserException;
}


class AsmKeyLexer extends Lexer;


options {
    // lookahead 3 is required for symbol '<-' versus '<->'.
    k = 3; 
    charVocabulary = '\1'..'\377';
    noConstructors = true;
    testLiterals = false;
}

tokens {
    /* quantifiers */
    FORALL = "all";
    EXISTS = "ex";

    /* literals */
    TRUE = "TRUE";
    FALSE = "FALSE";

    /* taclets */
    FIND = "find";
    IF = "if";
    CLOSE = "close";
    GOAL = "goal";
    SAMEUDPATELEVEL = "sameUpdateLevel";
    INSEQUENTSTATE = "inSequentState";
    REPLACEWITH = "replacewith";
    REPLACEBRANCH = "replacebranch";
    ADDRULES = "addrules";
    ADD = "add";
    BUILTIN = "builtin";
    /* cond */
    VARCOND = "varcond";
    COND = "cond";
    TYPEOF = "typeof";
    NEW = "new";
    OP = "op";
    NOT = "not";
    FREE = "free";
    PURE = "pure";
    DEPENDING = "depending";
    RIGID = "rigid";
    ON = "on";

    WARYEX = "waryEx";
    WARYALL = "waryAll";
    
    NONINTERACTIVE = "noninteractive";
    DISPLAYNAME = "displayname";
    HELPTEXT = "helptext";

    /* proof */
    META = "meta";
    HEADER = "header";
    NAME = "name";
    CLOSED = "closed";
    PROOF = "proof";
    DEPENDS = "depends";
    TERM = "term";
    BRANCH = "branch";
    INST = "inst";
    IFSEQFORMULA = "ifseqformula";
    INTERACTIVE = "interactive";
    HEUR = "heur";
    LOG = "keyLog";
    USER = "keyUser";
    VERSION = "keyVersion";
    AXIOM = "axiom";

    PROBLEM = "problem";
    IS = "is";

    /* declarations */
    UNIT = "unit";
    IMPORT = "import";
    EXPORT = "export";
    FROM = "from";
    SORT = "sort";
    DATA = "data";
    SCHEMA = "schema";
    VARIABLE = "variable";
    FORMULA = "formula";
    CONST = "const";
    PREDICATE = "predicate";
    TACLET = "taclet";
    LEMMA = "lemma";
    THEOREM = "theorem";
    PROPOSITION = "proposition";
    COROLLARY = "corollary";
    USE = "use";
    MAY = "may";
    ACCESS = "access";
    UPDATE = "update";
    DERIVED = "derived";

    RULE = "rule";
    SET = "set";
    SETS = "sets";

    ASM = "asm";
    DYNAMIC = "dynamic";
    STATIC = "static";
    STATICARGS = "staticargs";
    ATOMIC = "atomic";
    GENERIC = "generic";
    

    /* asm */
    ABSTRACT = "abstract";
    ASMSKIP = "skip";
    ASMTHEN = "then";
    ASMELSE = "else";
    ASMEND = "end";
    ASMIN = "in";
    ASMLET = "let";
    ASMFORALL = "forall";
    ASMWITH = "with";
    ASMDO = "do";
    ASMTRY = "try";
    ASMAND = "and";
    ASMOR = "or";
    ASMALSO = "also";
    ASMPAR = "par";
    ASMSEQ = "seq";

    /* big operator */

    BIGAND = "And";
    BIGOR = "Or";
    FUNCTION = "function";


    /* special idents */
    STEPIDENT;
    BIGIDENT;
    CAPITALIDENT;
}


{
    /* --- constructors --- */

    private AsmKeyLexer(Reader in, String filename) {
        this(in);
        this.filename = filename;
        this.in = in;
    }


    public AsmKeyLexer(File file) throws FileNotFoundException {
        this(new BufferedReader(new FileReader(file)), file.getName());
    }

    /* --- private fields --- */

    private String filename = null;
    private Reader in;

    /* --- public method --- */
    
    public String getFilename() {
        return filename;
    }

    public void close() {
        try {
            if (in != null) {
                in.close();
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

}

QUOTE
    : '\'';

SEMI
    : ';' ;

COLON
    : ':' ;

ASSIGN
    : ":=" ;

DOT
    : '.' ;

COMMA
    : ',' ;

LPAREN
    : '(' ;

RPAREN
    : ')' ;

LBRACE
    : '{' ;

RBRACE
    : '}' ;

LSETBRACK
    : "'[";

LBRACK
    : '[' ;

RBRACK
    : ']' ;

//LSEQBRACK
//    : "'<" ;

DLBRACK
    : "[[" ;

DRBRACK
    : "]]";

AT
    : '@' ;

OR
    : '|' ;

AND
    : '&' ;

NOT
    : '!' ;

IMP
    : "->" ;

EQV
    : "<->" ;

EQUALS
    : '=' ;

NOTEQUALS
    : "!=" ;

TERMEQUALS
    : "==" ;

LT
    : '<' ;

GT
    : '>' ;

DLT
    : "<<";

DGT
    : ">>";

SEQARROW
    : "==>" ;

PLUS
    : '+' ;

MINUS
    : '-' ;

ASTERIX
    : '*' ;

SLASH
    : '/';

UPDATE
    : "<-" ;

TIMED
    : '^' ;

QUESTION
    : '?';




protected
DIGIT
options {
    paraphrase = "a digit";
}
    : '0'..'9' ;

protected
LETTER
options {
    paraphrase = "a letter" ;
}
   : BIGLETTER | SMALLLETTER ;

protected
BIGLETTER
options {
    paraphrase = "a big letter";
}
    : 'A'..'Z' ;

protected
SMALLLETTER
options {
    paraphrase = "a small letter";
}
    : 'a'..'z' ;

protected 
IDSMALL 
options {
    paraphrase = "an admissible character for identifierssn with small first letter";
}
    : SMALLLETTER | DIGIT | '_' | '~' | '#' | '%';

protected
IDCHAR
options {
    paraphrase = "an admissible sequence of characters for middle of identifiers, 
    a normal ident may not finish with an underscore";
}
    : LETTER | DIGIT | '_' | '~'| '#' | '%';


/* remark: a identifer IDENT that ends with an underscore
 *         is promoted to IDENTTIMED, use for the explicit step logic
 */
IDENT
options {
    paraphrase = "an identifier";
    testLiterals = true;
}
    :
        BIGLETTER (IDCHAR)* {$setType(BIGIDENT);}
            ('.' ((IDSMALL {$setType(IDENT);} (c1:IDCHAR)*
                   {if (c1 != null && c1.getText().equals("_")) $setType(STEPIDENT);}) | 
                  (BIGLETTER {$setType(BIGIDENT);} (IDCHAR)*)))? 
    |
         IDSMALL (c2:IDCHAR)* {if (c2 != null && c2.getText().equals("_")) $setType(STEPIDENT);}
    ;


/* whitespace */
WS
options {
    paraphrase = "white space";
}
    :
        (
            ' '
        |
            '\t'
        |
            '\n' { newline(); }
        |
            '\r'
        )
        {
            $setType(Token.SKIP);
        }
    ;


/* single line comment */
SL_COMMENT
options {
    paraphrase = "a comment";
}
    :
        "//"
        (~'\n')* '\n'
        {
            $setType(Token.SKIP);
            newline();
        }
    ;


/* multi line comment */
ML_COMMENT
options {
    paraphrase = "a comment";
}
	:
        "/*"
		(
			options {
				generateAmbigWarnings=false;
			}
		:
			{ LA(2) != '/' }? '*'
		|	'\n' { newline(); }
		|	~( '*' | '\n' )
		)*
		"*/"
        {
            $setType(Token.SKIP);
        }
	;


STRING_LITERAL
options {
    paraphrase = "a string in double quotes";
}
    : '"'! ( ESC | ~('"'|'\\') )* '"'! ;


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


// Local variables:
// mode: Antlr
// End:
