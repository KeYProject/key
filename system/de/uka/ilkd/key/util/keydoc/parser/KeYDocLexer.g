// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
header { package de.uka.ilkd.key.util.keydoc.parser; }

class KeYDocLexer extends Lexer;


options { charVocabulary= '\u0000'..'\uFFFE'; k=2;
    exportVocab= KeYDocLexer;
        } // Allowered Unicode chars and lookahead

tokens {



SINCE= "since";

PROVABLE= "provable";

LINK= "link";

SEE= "see";

AUTHOR= "author";

VERSION= "version";

DEPRECATED= "deprecated";

STATISTIC= "statistic";

}


/* ***************** NOT TAGRELATED STUFF **********/
OPENDOC: "/**";

CLOSEDOC: "*/";
OTHERTEXT: (~('\r'|'\n'|'\t'|'{'|'@'|'/'|'0'..'9'|'a'..'z'|'A'..'Z'|'>'|'.'|'*'|'}'|'#'|'\"'|' '))+;

/* ***************** END NOT TAGRELATED STUFF *****/


    
/* **************** BASICS ************************/

IDENT options{ testLiterals = true; }: ('a'..'z' | 'A'..'Z')('a'..'z' | 'A'..'Z' | '0'..'9' )*;
    
INT: ('0'..'9')+;

DOT: '.';

QUOTE: '\"';

WS: ' ';

LEFTBRACKET: '{';

RIGHTBRACKET: '}';

HTTPSTART: "<a href=";

MT: ">";

HASH: '#';

SLASH: '/';

AT: '@';

STAR: '*';

TAB: '\t'; // necessary for ignoring at newline in parser.

NEWLINE
    : (('\r' '\n') // DOS
    | ('\n'      ) ) // UNIX
        { newline(); }
    ;
 


/* **************** END BASICS ********************/
