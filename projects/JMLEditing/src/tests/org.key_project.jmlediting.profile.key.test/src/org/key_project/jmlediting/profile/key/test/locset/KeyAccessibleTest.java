package org.key_project.jmlediting.profile.key.test.locset;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.parser.ParserTestUtils;
import org.key_project.jmlediting.profile.key.test.KeyProfileTestUtils;

public class KeyAccessibleTest {

   @Test
   public void parseDefaultAccessible1() {
      this.testParse("accessible \\everything;");
   }

   @Test
   public void parseDefaultAccessible2() {
      this.testParse("accessible x, y, a[*];");
   }

   @Test
   public void parseAccessibleLocStoreExpression() {
      this.testParse("accessible \\set_union(\\empty, x);");
   }

   @Test
   public void parseAccessibleModelSyntax1() {
      this.testParse("accessible test : \\everything;");
   }

   @Test
   public void parseAccessibleModelSyntax2() {
      this.testParse("accessible test : x, y, \\set_minus(x, x);");
   }

   @Test
   public void parseAccessibleModelSyntaxWithInv() {
      this.testParse("accessible \\inv : this.*;");
   }

   private void testParse(final String text) {
      try {
         ParserTestUtils.testParseComplete(text, KeyProfileTestUtils
               .keyProfile().createParser());
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

}
