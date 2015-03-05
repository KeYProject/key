grammar ProofCollectionParser;

@header {
package de.uka.ilkd.key.experimental;

import java.io.File;
}

@parser::members {
enum TestProperty{PROVABLE, NOTPROVABLE, LOADABLE}
}

parserEntryPoint
    : group*
;

group
    : 'group' Identifier '{' testDeclaration* '}'
;

testDeclaration returns [TestProperty testProperty, File file]
    : testPropertyDeclaration fileName
;

fileName returns [File file]
    : ( (Identifier | /* epsilon */ ) ('.' | '/') )* Identifier
;

testPropertyDeclaration returns [TestProperty ret]
    : Identifier
;

Identifier
    :  IdentifierStart (IdentifierStart | '0'..'9')*
;

fragment IdentifierStart
    :  'a'..'z' | 'A'..'Z' | '_' | '$'
;

// whitespace treatment (vorerst) kopiert von den antlr beispielen
// https://github.com/antlr/examples-v3/blob/master/java/java/Java.g

WS
    : (' '|'\r'|'\t'|'\u000C'|'\n')+ {$channel=HIDDEN;}
;

COMMENT
    : '/*' ( options {greedy=false;} : . )* '*/' {$channel=HIDDEN;}
;

LINE_COMMENT
    : ('//' | '#') ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;}
;

