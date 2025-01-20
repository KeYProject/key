lexer grammar RustySchemaLexer;

import RustyLexer;

TYPE_OF
    : 's#typeof'
    ;

SCHEMA_IDENTIFIER
    : 's#' NON_KEYWORD_IDENTIFIER
    ;

CONTEXT_START
    : 'c#'
    ;
CONTEXT_END
    : '#c'
    ;

PANIC
    : 'panic!'
    ;

 LOOP_SCOPE: 'loop_scope!';