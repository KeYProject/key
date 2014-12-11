package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;

public class LexicalHelperTest {

   @Test
   public void testParseDecimalConstants() throws ParserException {
      parseIntegerConstantTest("12345");
      parseIntegerConstantTest("8");
      parseIntegerConstantTest("823402l");
      parseIntegerConstantTest("234923L");
      parseIntegerConstantTest("243Ll", 4);
      parseIntegerConstantTest("938  ", 3);
   }

   @Test
   public void testParseOctalConstants() throws ParserException {
      parseIntegerConstantTest("0");
      parseIntegerConstantTest("0372l");
      parseIntegerConstantTest("02721341L");
      parseIntegerConstantTest("0237  ", 4);
      parseIntegerConstantTest("0369", 3);
   }

   @Test
   public void testParseHexConstants() throws ParserException {
      parseIntegerConstantTest("0x847AB");
      parseIntegerConstantTest("0xABB");
      parseIntegerConstantTest("0xA83Bl");
      parseIntegerConstantTest("0x992L");
      parseIntegerConstantTest("0x882L ", 6);
      parseIntegerConstantTest("0x83BBZ ", 6);
   }

   @Test
   public void parseInvalidConstants() {
      parseWrongConstantTest("X029");
      parseWrongConstantTest("");
      parseWrongConstantTest("0xI");
   }

   public static void parseIntegerConstantTest(final String constant)
         throws ParserException {
      parseIntegerConstantTest(constant, constant.length());
   }

   public static void parseIntegerConstantTest(final String constant,
         final int expectedEnd) throws ParserException {
      final int end = ParserBuilder.integerConstant()
            .parse(constant, 0, constant.length()).getEndOffset();
      assertEquals("Parse Integer Constant stopped at wrong position",
            expectedEnd, end);
   }

   public static void parseWrongConstantTest(final String constant) {
      try {
         parseIntegerConstantTest(constant);
      }
      catch (final ParserException e) {
         return;
      }
      fail("Parsing did not encounted an exception for " + constant);
   }

}
