package org.key_project.jmlediting.profile.key.test.other;

import static org.key_project.jmlediting.profile.key.test.utilities.JMLEditingKeYProfileTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class KeYBehaviorTest {

   @Test
   public void testBreakBehavior() throws ParserException {
      testParseComplete("break_behavior breaks;");
   }

   @Test
   public void testContinueBehavior() throws ParserException {
      testParseComplete("continue_behavior continues (x);");
   }

   @Test
   public void testReturnBehavior() throws ParserException {
      testParseComplete("return_behavior returns x == y;");
   }

}
