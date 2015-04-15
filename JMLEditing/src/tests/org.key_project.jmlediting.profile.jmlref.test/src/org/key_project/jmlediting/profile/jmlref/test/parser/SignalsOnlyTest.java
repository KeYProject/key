package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class SignalsOnlyTest {

   /**
    * signals-only-clause ::= <br>
    * signals-only-keyword reference-type [ , reference-type ] ... ; <br>
    * | signals-only-keyword \nothing ;
    *
    * signals-only-keyword ::= signals_only | signals_only_redundantly
    */

   @Test
   public void testSignalsOnlyNothing() throws ParserException {
      testParseComplete("signals_only \\nothing;");
   }

   @Test
   public void testSignalsOnlyOneReferenceType() throws ParserException {
      testParseComplete("signals_only_redundantly NullPointerException;");
   }

   @Test
   public void testSignalsOnlyMultipleTypes() throws ParserException {
      testParseComplete("signals_only NullPointerException, IllegalArgumentException;");
   }

}
