package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.quantifier.QuantifierPrimary;
import org.key_project.jmlediting.profile.jmlref.test.utilities.ProfileWrapper;

public class QuantifierParserTest {

   @Test
   public void testForall() {
      testParse("(\\forall int i; i < 5)");
   }

   @Test
   public void testQuantifiedExisits() {
      testParse("(\\exists String s1,s1; s1.length > s2.length; s1.equals(\"\"))");
   }

   @Test
   public void testEmptyQuantifiedSum() {
      testParse("(\\sum double d;; x.contains(d))");
   }

   @Test
   public void testProductArray() {
      testParse("(\\product Object[] x; x.length)");
   }

   @Test
   public void testNumOfNullable() {
      testParse("(\\num_of nullable Integer i; x.equals(i))");
   }

   @Test
   public void testMinNonNull() {
      testParse("(\\min non_null String s; s.length < 5; s.length -1)");
   }

   @Test
   public void testNestedQuantifiers() {
      testParse("(\\forall int x; (\\exists int y; y > x; foo(y)); bar(x))");
   }

   @Test
   public void non_nullTypeNeedsModifier() {
      testParseFail("(\\forall non_null x; true)");
   }

   @Test
   public void non_nullTypeWithModifier() {
      testParse("(\\exists nullable non_null y; y.isNull())");
   }

   private static void testParse(final String content) {
      try {
         testParseEx(content);
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

   private static void testParseEx(final String content) throws ParserException {

      final QuantifierPrimary primary = new QuantifierPrimary();
      primary.setProfile(ProfileWrapper.testProfile);
      ParserBuilder.requireComplete(primary)
            .parse(content, 0, content.length()).prettyPrintAST();

   }

   private static void testParseFail(final String content) {
      try {
         testParseEx(content);
      }
      catch (final ParserException e) {
         return;
      }
      fail();
   }

}
