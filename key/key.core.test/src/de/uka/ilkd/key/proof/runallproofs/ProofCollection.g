grammar ProofCollection;

@lexer::header {
package de.uka.ilkd.key.proof.runallproofs;
}

@parser::header {
package de.uka.ilkd.key.proof.runallproofs;
}

/*
 * Section for parser rules. Parser rules start with lowercase letters.
 */

parserEntryPoint returns [List<ProofCollectionUnit> units, ProofCollectionSettings globalSettings]
@init {
    $units = new ArrayList<>();
    //$globalSettings = ProofCollectionSettings.getDefaultSettings(getTokenStream().getSourceName());
    $globalSettings = new ProofCollectionSettings(getTokenStream().getSourceName());
}
    : settingAssignment[$globalSettings]*
    
      ( g=group[$globalSettings] {$units.add(g);}
      | t=testDeclaration {$units.add(new SingletonProofCollectionUnit(t));} )*
      
      EOF
;

group[ProofCollectionSettings globalSettings] returns [ProofCollectionUnit unit]
@init{
    ProofCollectionSettings localSettings = new ProofCollectionSettings(globalSettings);
    List<TestFile> files = new ArrayList<>();
}
    : 'group' nameToken=Identifier
      '{'
          settingAssignment[localSettings]*
          (t=testDeclaration {files.add(t);} )*
      '}'
      {unit = new GroupedProofCollectionUnit(nameToken.getText(), localSettings, files);}
;

settingAssignment[ProofCollectionSettings settings]
    : key=Identifier '=' value=(Identifier | PathString | QuotedString | Number)
      {settings.put(key.getText(), value.getText());}
;

testDeclaration returns [TestFile file]
@init{TestProperty testProperty = null;}
    : 
      ('provable' {testProperty=TestProperty.PROVABLE;}
      | 'notprovable' {testProperty=TestProperty.NOTPROVABLE;}
      | 'loadable' {testProperty=TestProperty.LOADABLE;})
      
      ':'? // double colon is optional (doesn't hurt if omitted)
       
      pathToken=(PathString | Identifier | Number)
      {
        assert testProperty != null: "Parser should have assigned a value other that null to variable testProperty at this point.";
        file = new TestFile(testProperty, pathToken);
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
