package org.key_project.jmlediting.profile.key.test.spec_statement;

import static org.key_project.jmlediting.profile.key.test.utilities.JMLEditingKeYProfileTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class SpecStatementsTest {

   @Test
   public void testReturnsEmpty() throws ParserException {
      testParseComplete("returns;");
   }

   @Test
   public void testContinuesEmptyLabel() throws ParserException {
      testParseComplete("continues () ;");
   }

   @Test
   public void testBreaksPredicate() throws ParserException {
      testParseComplete("breaks x < y;");
   }

   @Test
   public void testContinuesEmptyLabelPredicate() throws ParserException {
      testParseComplete("continues () true;");
   }

   @Test
   public void testBreaksLabel() throws ParserException {
      testParseComplete("breaks (label);");
   }

   @Test
   public void testContinuesLabelPredicate() throws ParserException {
      testParseComplete("continues (label) pred == pred;");
   }

   @Test(expected = ParserException.class)
   public void testJMLRefNotSupported() throws ParserException {
      testParseComplete("continues (x) -> hallo;");
   }

}
