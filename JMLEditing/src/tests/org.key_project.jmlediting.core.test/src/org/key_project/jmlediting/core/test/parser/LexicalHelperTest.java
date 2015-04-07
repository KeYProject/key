package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.*;
import static org.key_project.jmlediting.core.dom.Nodes.createString;
import static org.key_project.jmlediting.core.parser.util.Lexicals.*;
import static org.key_project.jmlediting.core.test.utilities.ParserTestUtils.*;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.utilities.ParserTestUtils;

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

   @Test
   public void testIntegerConstant() throws ParserException {
      testParse("1234", integerLiteral(), createString(0, 4, "1234"));
   }

   @Test
   public void testIntegerConstantWithWhitespaces() throws ParserException {
      testParse("  12323sh", integerLiteral(), createString(2, 7, "12323"));
   }

   @Test
   public void testIntegerConstantFail() {
      testParseFail(" sj", integerLiteral());
   }

   @Test
   public void testIntegerConstantEmpty() {
      testParseFail("", integerLiteral());
   }

   @Test
   public void testParseFloatConstant() throws ParserException {
      testParseFloatConstant("1232.");
      testParseFloatConstant(".94584");
      testParseFloatConstant("1232.12382");
      testParseFloatConstant("0128.");
   }

   @Test
   public void testParseFloatConstantExponent() throws ParserException {
      testParseFloatConstant("0002e3");
      testParseFloatConstant(".03e-56");
      testParseFloatConstant("2.3e+0");
   }

   @Test
   public void testParseFloatConstantTypeSuffix() throws ParserException {
      testParseFloatConstant("022d");
      testParseFloatConstant("9f");
      testParseFloatConstant("213F");
      testParseFloatConstant("92349D");
      testParseFloatConstant("9392.23490e+93F");
      testParseFloatConstant(".0e0d");
   }

   @Test
   public void testParseIntAsFloat() {
      testParseInvalidFloat("4");
   }

   @Test
   public void testParseEmptyFloat() {
      testParseInvalidFloat("");
   }

   @Test
   public void testParseFloatWithHex() {
      testParseInvalidFloat("22A.03");
   }

   @Test
   public void testParseIncompleteExponent() {
      testParseInvalidFloat("223e");
   }

   @Test
   public void testParseIncompleteExponent2() {
      testParseInvalidFloat("223e-");
   }

   @Test
   public void testParseWrongSuffix() {
      testParseInvalidFloat("223g");
   }

   @Test
   public void testParseCharLiteral() throws ParserException {
      testParseCharLiteral("\'a\'");
      testParseCharLiteral("\'C\'");
      testParseCharLiteral("\'D\'");
      testParseCharLiteral("\'l\'");
   }

   @Test
   public void testParseCharEscapes() throws ParserException {
      testParseCharLiteral("\'\\b\'");
      testParseCharLiteral("\'\\t\'");
      testParseCharLiteral("\'\\n\'");
      testParseCharLiteral("\'\\r\'");
      testParseCharLiteral("\'\\\'\'");
      testParseCharLiteral("\'\\\"\'");
      testParseCharLiteral("\'\\\\\'");
   }

   @Test
   public void testParseCharOctalEscapes() throws ParserException {
      testParseCharLiteral("\'\\0\'");
      testParseCharLiteral("\'\\2\'");
      testParseCharLiteral("\'\\53\'");
      testParseCharLiteral("\'\\123\'");
   }

   @Test
   public void testParseCharUnicodeEscapes() throws ParserException {
      testParseCharLiteral("\'\\uFFFF\'");
      testParseCharLiteral("\'\\u02BF\'");
      testParseCharLiteral("\'\\u93FF\'");
      testParseCharLiteral("\'\\u0000\'");
   }

   @Test
   public void testInvalidCharLiterals() {
      testParseInvalidChar("\'aa\'");
      testParseInvalidChar("\'\'");
      testParseInvalidChar("f\'");
      testParseInvalidChar("\'G");
   }

   @Test
   public void testInvalidCharEscapes() {
      testParseInvalidChar("\'\n\'");
      testParseInvalidChar("\'\r\'");
      testParseInvalidChar("\'\\\'");
   }

   @Test
   public void testInvalidCharOctalEscapes() {
      testParseInvalidChar("\'\\'");
      testParseInvalidChar("\'\\455\'");
      testParseInvalidChar("\'\\49'");
   }

   @Test
   public void testInvalidCharUnicodeEscapes() {
      testParseInvalidChar("\'\\u39\'");
      testParseInvalidChar("\'\\u93821\'");
      testParseInvalidChar("\'\\u9a21\'");
      testParseInvalidChar("\'\\u'");
   }

   @Test
   public void testParseStrings() throws ParserException {
      testParseStringLiteral("\"ashdjs\"");
      testParseStringLiteral("\"hallo mein name ist hase\"");
      testParseStringLiteral("\"Ja slJ kJS    ksl;kj Sjk/sf/nskj \"");
   }

   @Test
   public void testParseStringsWithEscapes() throws ParserException {
      testParseStringLiteral("\"\"");
      testParseStringLiteral("\"jas\\\" sdf\"");
      testParseStringLiteral("\"\\\\ sj\"");
      testParseStringLiteral("\"\b sjd \\u9283 kd sl \t \\n \' \\\" \043\"");
   }

   @Test
   public void testWrongString() {
      testParseInvalidString("\"jsaj");
      testParseInvalidString("asj\"");
      testParseInvalidString("\'skds\"");
      testParseInvalidString("\"\'");
      testParseInvalidString("\"\n\"");
      testParseInvalidString("\"\r\"");
      testParseInvalidString("\"\\\"");
   }

   @Test
   public void testParseSingleLineComment() throws ParserException {
      testParseComplete(" //    \n  123  ", integerLiteral(),
            "String[10-13](123)");
   }

   @Test
   public void testParseSingleLineCommentInLastLine() throws ParserException {
      testParseComplete(" //    \n  123 //  ", integerLiteral(),
            "String[10-13](123)");
   }

   public static void parseIntegerConstantTest(final String constant)
         throws ParserException {
      parseIntegerConstantTest(constant, constant.length());
   }

   public static void parseIntegerConstantTest(final String constant,
         final int expectedEnd) throws ParserException {
      final int end = integerLiteral().parse(constant, 0, constant.length())
            .getEndOffset();
      assertEquals("Parse Integer Constant stopped at wrong position",
            expectedEnd, end);
   }

   private static void testParseFloatConstant(final String textString)
         throws ParserException {
      testParseLiteral(textString, floatLiteral());
   }

   private static void testParseInvalidFloat(final String text) {
      testParseInvalidLiteral(text, floatLiteral());
   }

   private static void testParseCharLiteral(final String textString)
         throws ParserException {
      testParseLiteral(textString, characterLiteral());
   }

   private static void testParseInvalidChar(final String text) {
      testParseInvalidLiteral(text, characterLiteral());
   }

   private static void testParseStringLiteral(final String textString)
         throws ParserException {
      testParseLiteral(textString, stringLiteral());
   }

   private static void testParseInvalidString(final String text) {
      testParseInvalidLiteral(text, stringLiteral());
   }

   private static void testParseLiteral(final String textString,
         final ParseFunction parser) throws ParserException {
      ParserTestUtils.testParseComplete(textString, parser, "String[0-"
            + textString.length() + "](" + textString + ")");
   }

   private static void testParseInvalidLiteral(final String text,
         final ParseFunction function) {
      ParserTestUtils.testParseFail(text,
            ParserBuilder.requireComplete(function));
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
