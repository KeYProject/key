package org.key_project.jmlediting.profile.key.test.other;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.parser.ParserTestUtils;
import org.key_project.jmlediting.profile.key.other.DynamicLogicPrimary;

public class DynamicLogicPrimaryTest {

   @Test
   public void testParseDynamicLogic() {
      this.testParse(
            "\\dl_abc(XYZ)",
            "KeywordAppl[0-12](Keyword[0-4](\\dl_),KeywordContent[4-12](String[4-7](abc),String[8-11](XYZ)))");
   }

   @Test
   public void testParseDynamicLogicWithLayout() {
      this.testParse("         \\dl_abc(XYZ)");
   }

   private void testParse(final String text) {
      try {
         ParserTestUtils.testParseComplete(text, new DynamicLogicPrimary());
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

   private void testParse(final String text, final String expectedResult) {
      try {
         ParserTestUtils.testParseComplete(text, new DynamicLogicPrimary(),
               expectedResult);
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

}
