package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class SpecificationStatementTest {

   @Test
   public void testParseEmptyContinues() throws ParserException {
      testParseComplete("continues;");
   }

   @Test
   public void testParseTargetLabelContinues() throws ParserException {
      testParseComplete("continues -> (xyz);");
   }

   @Test
   public void testParsePredContinues() throws ParserException {
      testParseComplete("continues x > y;");
   }

   @Test
   public void testParseNotSpecifiedContinues() throws ParserException {
      testParseComplete("continues_redundantly \\not_specified;");
   }

   @Test
   public void testParseTargetLabelPredContinues() throws ParserException {
      testParseComplete("continues -> (abcde) x + y() == 2;");
   }

   @Test
   public void testParseEmptyBreaks() throws ParserException {
      testParseComplete("breaks;");
   }

   @Test
   public void testParseTargetLabelBreaks() throws ParserException {
      testParseComplete("breaks->(xyz);");
   }

   @Test
   public void testParsePredBreaks() throws ParserException {
      testParseComplete("breaks_redundantly false;");
   }

   @Test
   public void testParseNotSpecifiedBreaks() throws ParserException {
      testParseComplete("breaks \\not_specified;");
   }

   @Test
   public void testParseTargetLabelPredBreaks() throws ParserException {
      testParseComplete("breaks -> (abcde) x + y() == 2;");
   }

   @Test
   public void testParseEmptyReturns() throws ParserException {
      testParseComplete("returns ;");
   }

   @Test
   public void testParsePredReturns() throws ParserException {
      testParseComplete("returns a.b().c().d() > x;");
   }

   @Test
   public void testParseNotSpecifiedReturns() throws ParserException {
      testParseComplete("returns \\not_specified;");
   }

}
