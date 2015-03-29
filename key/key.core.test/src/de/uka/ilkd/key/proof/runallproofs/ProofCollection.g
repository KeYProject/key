grammar ProofCollection;

@lexer::header {
package de.uka.ilkd.key.proof.runallproofs;
}

@parser::header {
package de.uka.ilkd.key.proof.runallproofs;

import de.uka.ilkd.key.experimental.*;
import java.util.Map;
import java.util.HashMap;
}

/*
 * Section for parser rules. Parser rules start with lowercase letters.
 */

parserEntryPoint returns [List<ProofCollectionUnit> units, Map<Token, Token> settingsMap]
@init{
    $units = new ArrayList<>();
    $settingsMap = new HashMap<Token, Token>();
}
    : (g=group {$units.add(g);}
      | t=testDeclaration {$units.add(new SingletonProofCollectionUnit(t));} 
      | settingAssignment[$settingsMap])*
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

/*
 * Section for non-whitespace lexer rules. Lexer rules start with uppercase letters.
 * Whitespace rules can be found at the end of the file. I put them in a separate section, since
 * they are written to hidden channel.
 */

Identifier
    :  IdentifierStart( IdentifierStart | Digit | '.')*
;

Number
    : Digit+
;

QuotedString
    : '"' (EscapedQuote | ~('\\' | '"'))* '"'
;

/*
 * This lexer rule is for a string that is neither quoted, nor an identifier or a number.
 * As its name suggests, intended use is to allow specifying path names.
 * Note: There is a (seemingly inevitable) overlap with Number and Identifier lexer rules.
 *       Depending on input, lexer might create an Identifier token at a place where a path name is expected.
 *       This is considered in parser rule testDeclaration.
 */
PathString
    : (~('\n' | '\r' | '}' | '{' | '=' | ' ' | '\t' | ':' | '"' | '\\') | EscapedQuote)+
;

/*
 * Fragment rules. Those are neither parser nor lexer rules. No token types are created from them.
 * Those are merely reusable parts of lexer code, to help keeping the code clean.
 */

fragment EscapedQuote
    : '\\' ('\\' | '"')
;

fragment IdentifierStart
    : 'a'..'z' | 'A'..'Z' | '_' | '$'
;

fragment Digit
    : '0'..'9'
;

/*
 * Whitespace rules. Template from: https://github.com/antlr/examples-v3/blob/master/java/java/Java.g
 */

WS
    : (' '|'\r'|'\t'|'\u000C'|'\n')+ {$channel=HIDDEN;}
;

COMMENT
    : '/*' ( options {greedy=false;} : . )* '*/' {$channel=HIDDEN;}
;

LINE_COMMENT
    : ('//' | '#') ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;}
;

