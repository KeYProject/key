lexer grammar RustyWhileSchemaLexer;

import RustyWhileLexer;

SCHEMA_IDENTIFIER
    : 's#' NON_KEYWORD_IDENTIFIER
    ;

CONTEXT_START
    : 'c#'
    ;
CONTEXT_END
    : '#c'
    ;