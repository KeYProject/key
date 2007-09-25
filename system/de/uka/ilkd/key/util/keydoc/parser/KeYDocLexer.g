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
