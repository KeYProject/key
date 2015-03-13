grammar ProofCollection;

@lexer::header {
package de.uka.ilkd.key.experimental;
}

@parser::header {
package de.uka.ilkd.key.experimental;

import java.util.Map;
import java.util.HashMap;
}

parserEntryPoint returns [List<ProofCollectionUnit> units]
@init{units = new ArrayList<>();}
    : (g=group {units.add(g);} | t=testDeclaration {units.add(new SingletonProofCollectionUnit(t));} )*
;

group returns [ProofCollectionUnit unit]
@init{
    Map<Token, Token> settingsMap = new HashMap<Token, Token>();
    List<FileWithTestProperty> files = new ArrayList<>();
}
    : 'group' nameToken=Identifier
      '{'
          (settingAssignment[settingsMap] | t=testDeclaration {files.add(t);} )*
      '}'
      {unit = new GroupedProofCollectionUnit(nameToken, settingsMap, files);}
;

settingAssignment[Map<Token, Token> settingsMap]
    : key=Identifier '=' value=(Identifier | PathString | QuotedString | Number)
      {settingsMap.put(key, value);}
;

testDeclaration returns [FileWithTestProperty file]
@init{TestProperty testProperty = null;}
    : ('provable' {testProperty=TestProperty.PROVABLE;}
      | 'notprovable' {testProperty=TestProperty.NOTPROVABLE;}
      | 'loadable' {testProperty=TestProperty.LOADABLE;}) ':'?
      pathToken=(PathString | Identifier | Number)
      {
        assert testProperty != null: "Parser should have assigned a value other that null to variable testProperty at this point.";
        file = new FileWithTestProperty(testProperty, pathToken);
      }
;

Identifier
    :  IdentifierStart( IdentifierStart | Digit | '.')*
;

Number
    : Digit+
;

QuotedString
    : '"' (EscapedQuote | ~('\\' | '"'))* '"'
;

PathString
    : (~('\n' | '\r' | '}' | '{' | '=' | ' ' | '\t' | ':' | '"' | '\\') | EscapedQuote)+
;

fragment EscapedQuote
    : '\\' ('\\' | '"')
;

fragment IdentifierStart
    : 'a'..'z' | 'A'..'Z' | '_' | '$'
;

fragment Digit
    : '0'..'9'
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

