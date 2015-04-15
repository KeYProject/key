package org.key_project.jmlediting.profile.key.test.other;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.utilities.ParserTestUtils;
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;
import org.key_project.jmlediting.profile.key.other.DynamicLogicPrimary;
import org.key_project.jmlediting.profile.key.test.utilities.JMLEditingKeYProfileTestUtils;

public class DynamicLogicPrimaryTest {

   @Test
   public void testParseDynamicLogic() {
      this.testParse(
            "\\dl_abc(XYZ)",
            "KeywordAppl[0-12](Keyword[0-4](\\dl_),KeywordContent[4-12](String[4-7](abc),Some[7-12](ExpressionList[8-11](Primary[8-11](Identifier[8-11](String[8-11](XYZ)))))))");
   }

   @Test
   public void testParseDynamicLogicWithLayout() {
      this.testParse("         \\dl_abc(XYZ)");
   }

   @Test
   public void testDynamicLogicEmptySet() {
      this.testParse("\\dl_emptySet()");
   }

   @Test
   public void testDynamicLogicSingle() {
      this.testParse("\\dl_single(value)");
   }

   @Test
   public void testDynamicLogicCupSimple() {
      this.testParse("\\dl_cup(left.values,right.values)");
   }

   @Test
   public void testDynamicLogicComplex() {
      this.testParse(" \\dl_cup(\\dl_single(value), \n"
            + " @           (left==null)? \\dl_emptySet() \n"
            + " @                       : \\dl_cup(left.values,right.values))");
   }

   private void testParse(final String text) {
      try {
         final JMLReferenceProfile profile = JMLEditingKeYProfileTestUtils.keyProfile();
         final DynamicLogicPrimary primary = new DynamicLogicPrimary();
         primary.setProfile(profile);
         ParserTestUtils.testParseComplete(text, primary);
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

   private void testParse(final String text, final String expectedResult) {
      try {
         final JMLReferenceProfile profile = JMLEditingKeYProfileTestUtils.keyProfile();
         final DynamicLogicPrimary primary = new DynamicLogicPrimary();
         primary.setProfile(profile);
         ParserTestUtils.testParseComplete(text, primary, expectedResult);
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

}
