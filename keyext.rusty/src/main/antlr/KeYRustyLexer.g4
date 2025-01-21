lexer grammar KeYRustyLexer;

import KeYLexer;
@ header
{
package org.key_project.rusty.parser;
}

MUT : 'mut';

MUTATE
:   '*->'
    ;

REF_M : 'refM';

NEW_LOCAL_VARS: '\\newLocalVars';
STORE_TERM_IN : '\\storeTermIn';
STORE_EXPR_IN : '\\storeExprIn';
HAS_INVARIANT : '\\hasInvariant';
GET_INVARIANT : '\\getInvariant';
GET_VARIANT   : '\\getVariant';
IS_LABELED    : '\\isLabeled';
DIFFERENT     : '\\different';