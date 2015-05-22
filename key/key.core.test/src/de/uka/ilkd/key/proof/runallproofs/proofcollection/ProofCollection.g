grammar ProofCollection;

@lexer::header {
package de.uka.ilkd.key.proof.runallproofs.proofcollection;
}

@parser::header {
package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
}

/*
 * Section for parser rules. Parser rules start with lowercase letters.
 */

// see also: http://stackoverflow.com/questions/2445008/how-to-get-antlr-3-2-to-exit-upon-first-error
@parser::members {
  @Override
  protected Object recoverFromMismatchedToken(IntStream input, int ttype, BitSet follow) throws RecognitionException {
    throw new MismatchedTokenException(ttype, input);
  }

  @Override
  public Object recoverFromMismatchedSet(IntStream input, RecognitionException e, BitSet follow) throws RecognitionException {
    throw e;
  }
}

@rulecatch {
  catch (RecognitionException e) {
    throw e;
  }
}

@lexer::members {
  @Override
  public void reportError(RecognitionException e) {
    throw new RuntimeException(e);
  }
}

parserEntryPoint returns [ProofCollection proofCollection]
@init {
    List<ProofCollectionUnit> proofCollectionUnits = new ArrayList<>();
    List<ProofCollectionSettings.Entry> settingsEntries = new ArrayList<>();
}
    : settingAssignment[settingsEntries]*
    
      ( g=group { proofCollectionUnits.add(g); }
      | t=testDeclaration { proofCollectionUnits.add(new SingletonProofCollectionUnit(t)); } )*
      
      EOF
      { 
         /*
          * Because settings objects are immutable, we have to collect all settings entries
          * in a list first and process them when parsing is finished.
          */ 
         ProofCollectionSettings globalSettings =
         new ProofCollectionSettings(getTokenStream().getSourceName(), settingsEntries);
         $proofCollection = new ProofCollection(proofCollectionUnits, globalSettings);
      }
;

group returns [ProofCollectionUnit unit]
@init{
    List<TestFile> files = new ArrayList<>();
    
    // groups can have their own local settings 
    List<ProofCollectionSettings.Entry> settingsEntries = new ArrayList<>();
}
    : 'group' nameToken=Identifier
      '{'
          settingAssignment[settingsEntries]*
          (t=testDeclaration {files.add(t);} )*
      '}'
      {unit = new GroupedProofCollectionUnit(nameToken.getText(), settingsEntries, files);}
;

settingAssignment[List<ProofCollectionSettings.Entry> settingsEntries]
    @init {
      String key;
      String value = null;
    }
    : k = Identifier { key = k.getText(); } '=' 
      ( v = (Identifier | PathString | Number) { value = v.getText(); }
      | v = QuotedString { String tmp = v.getText(); value = tmp.substring(1, tmp.length() - 1); } )
      { 
         settingsEntries.add(new ProofCollectionSettings.Entry(key, value));
      }
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
