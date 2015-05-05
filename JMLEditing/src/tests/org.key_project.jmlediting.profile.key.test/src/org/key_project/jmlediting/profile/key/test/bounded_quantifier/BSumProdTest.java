package org.key_project.jmlediting.profile.key.test.bounded_quantifier;

import static org.key_project.jmlediting.profile.key.test.utilities.JMLEditingKeYProfileTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class BSumProdTest {

   @Test
   public void testParseBSum() throws ParserException {
      testParseComplete("ensures x == (\\bsum int i; 0; 100; i);");
   }

   @Test
   public void testParseBProd() throws ParserException {
      testParseComplete("requires (\\bprod int j; Math.random(); Math.random(); sqrt(j));");
   }

}
