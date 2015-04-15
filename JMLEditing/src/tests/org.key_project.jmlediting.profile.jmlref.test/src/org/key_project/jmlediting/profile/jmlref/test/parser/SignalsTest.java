package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class SignalsTest {

   /**
    * signals-clause ::= <br>
    * signals-keyword ( reference-type [ ident ] ) [ pred-or-not ] ;<br>
    *
    * signals-keyword ::= signals | signals_redundantly | exsures |
    * exsures_redundantly
    */

   @Test
   public void testSignalsReferenceType() throws ParserException {
      testParseComplete("signals (NullPointerException);");
   }

   @Test
   public void testSignalsReferenceTypeWithIdent() throws ParserException {
      testParseComplete("signals (ArrayOutOfBoundsException ex);");
   }

   @Test
   public void testSignalsWithPredicate() throws ParserException {
      testParseComplete("exsures (Exception e) e.getMessage().equals(\"Hallo\");");
   }

   @Test
   public void testSignalsNotSpecified() throws ParserException {
      testParseComplete("signals_redundantly (Error e) \\not_specified;");
   }

}
