package org.key_project.jmlediting.profile.key.test.other;

import static org.key_project.jmlediting.profile.key.test.utilities.JMLEditingKeYProfileTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class ElemsTest {

   @Test
   public void testParseNonNullElems() throws ParserException {
      testParseComplete("requires \\nonnullelements(x);");
   }

   @Test
   public void testParseNonNullElemsMultipleLocations() throws ParserException {
      testParseComplete("requires \\nonnullelements(x, y.*);");
   }

   @Test
   public void testParseNewElemsFresh() throws ParserException {
      testParseComplete("requires \\new_elems_fresh(a[*]);");
   }

}
