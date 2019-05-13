grammar ProofCollection;

@lexer::header {
package de.uka.ilkd.key.proof.runallproofs.proofcollection;
}

@parser::header {
package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import java.util.Map.Entry;
import static de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings.getSettingsEntry;
import java.util.Date;
}

/*
 * Section for parser rules. Parser rules start with lowercase letters.
 */

// see also: http://stackoverflow.com/questions/2445008/how-to-get-antlr-3-2-to-exit-upon-first-error
@parser::members {

  public final Date runStart = new Date(System.currentTimeMillis());

  @Override
  protected Object recoverFromMismatchedToken(IntStream input, int ttype, BitSet follow) throws RecognitionException {
    throw new MismatchedTokenException(ttype, input);
  }

  @Override
  public Object recoverFromMismatchedSet(IntStream input, RecognitionException e, BitSet follow) throws RecognitionException {
    throw e;
  }
  
  /*
   * This method just calls a constructor. We need this method so we can call a different constructor
   * in a parser subclass.
   */
  public TestFile getTestFile(TestProperty testProperty, String path, ProofCollectionSettings settings) {
    return TestFile.createInstance(testProperty, path, settings);
  }
}

@rulecatch {
  catch (RecognitionException e) {
    throw e;
  }
}

//@lexer::members {
//  @Override
//  public void recover(RecognitionException e) throws RecognitionException {
//    super.recover(e);
//    throw e;
//  }
//}

parserEntryPoint returns [ProofCollection proofCollection]
@init {
    List<Entry<String, String>> settingsEntries = new ArrayList<>();
}
    : settingAssignment[settingsEntries]*
    {
        // Create global settings.
        final ProofCollectionSettings globalSettings =
            new ProofCollectionSettings(getTokenStream().getSourceName(), settingsEntries, runStart);
        $proofCollection = new ProofCollection(globalSettings);
    }
    (
        g=group[globalSettings] { $proofCollection.add(g); }
        | file=testFile[globalSettings] 
        {
            $proofCollection.add(new SingletonProofCollectionUnit(file, globalSettings));
        }
    )*
    EOF
;

settingAssignment[List<Entry<String, String>> settingsEntries]
    @init {
      String key;
      String value = null;
    }
    : k = Identifier { key = k.getText(); } '=' 
    v = valueDeclaration { value = v; }
    { 
        settingsEntries.add(getSettingsEntry(key, value));
    }
;

valueDeclaration returns [String value]
    : ( v = (Identifier | PathString | Number) { value = v.getText(); } ) |
    (
        v = QuotedString
        {
            String tmp = v.getText();
            value = tmp.substring(1, tmp.length() - 1);
        }
    )
;

group[ProofCollectionSettings settings] returns [ProofCollectionUnit unit]
@init{
    List<TestFile> files = new ArrayList<>();

    // groups can have their own local settings 
    List<Entry<String, String>> settingsEntries = new ArrayList<>();
}
    : 'group' nameToken=Identifier
    '{'
        settingAssignment[settingsEntries]*
        {
            // Create local settings object.
            settings = new ProofCollectionSettings(settings, settingsEntries);
        }

        ( t=testFile[settings]  {files.add(t);} )*
    '}'
    {
        unit = new GroupedProofCollectionUnit(nameToken.getText(), settings, files);
    }
;

testFile[ProofCollectionSettings settings]  returns [TestFile file]
@init{
    TestProperty testProperty = null;
}
    : 
    (
        'provable' {testProperty=TestProperty.PROVABLE;}
        | 'notprovable' {testProperty=TestProperty.NOTPROVABLE;}
        | 'loadable' {testProperty=TestProperty.LOADABLE;}
    )
    { assert testProperty != null: "Parser should have assigned a value other that null to variable testProperty at this point."; }
    ':'? // double colon is optional (doesn't hurt if omitted)
    path = valueDeclaration
    {
        file = getTestFile(testProperty, path, settings);
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
