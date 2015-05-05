package org.key_project.jmlediting.profile.key.test.other;

import static org.key_project.jmlediting.profile.key.test.utilities.JMLEditingKeYProfileTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class OverridenKeywordTest {

   @Test
   public void testReachKeyword1() throws ParserException {
      testParseComplete("ensures \\reach(a, a < b, b.length) != \\empty;");
   }

   @Test
   public void testReachKeyword2() throws ParserException {
      testParseComplete("ensures \\reach(a, a < b, b.length, i++) != \\empty;");
   }

   @Test
   public void testDecreasing() throws ParserException {
      testParseComplete("decreasing x, y, z;");
   }

   @Test
   public void testMeasuredBy() throws ParserException {
      testParseComplete("measured_by x, y, z;");
   }

}
