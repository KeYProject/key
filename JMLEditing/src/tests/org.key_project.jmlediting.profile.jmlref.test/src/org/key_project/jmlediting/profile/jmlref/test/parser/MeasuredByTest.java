package org.key_project.jmlediting.profile.jmlref.test.parser;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.*;

public class MeasuredByTest {

   /**
    * measured-clause ::= <br>
    * measured-by-keyword \not_specified ;<br>
    * | measured-by-keyword spec-expression [ if predicate ] ;<br>
    *
    * measured-by-keyword ::= measured_by | measured_by_redundantly
    */

   @Test
   public void testMeasuredByNotSpecified() throws ParserException {
      testParseComplete("measured_by \\not_specified;");
   }

   @Test
   public void testMeasuredBySpecExpression() throws ParserException {
      testParseComplete("measured_by array.length;");
   }

   @Test
   public void testMeasuredByWithIf() throws ParserException {
      testParseComplete("measured_by array.length if array != null;");
   }

}
