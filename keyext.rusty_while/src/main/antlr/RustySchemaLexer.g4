lexer grammar RustySchemaLexer;

import RustyLexer;

SCHEMA_IDENTIFIER
    : 's#' NON_KEYWORD_IDENTIFIER
    ;

CONTEXT_START
    : 'c#'
    ;
CONTEXT_END
    : '#c'
    ;

TYPE_OF
    : 's#typeof'
    ;