package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.ParserUtils;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefParser;

public class StoreRefParserTest {

   @Test
   public void testParseNothingKeyword() throws ParserException {
      testParse(" \\nothing", "StoreRefList[1-9](Keyword[1-9](\\nothing))");
   }

   @Test
   public void testEverythingKeyword() throws ParserException {
      testParse("\t \\everything  ",
            "StoreRefList[2-13](Keyword[2-13](\\everything))");
   }

   @Test
   public void testParseSimpleIdentifier() throws ParserException {
      testParse(
            " state ",
            "StoreRefList[1-6](List[1-6](StoreRefExpr[1-6](String[1-6](state),List[6-6]())))");
   }

   @Test
   public void testParseQualifiedIdentifier() throws ParserException {
      testParse(
            " this.state . action",
            "StoreRefList[1-20](List[1-20](StoreRefExpr[1-20](String[1-5](this),List[6-20](StoreRefNameSuffix[6-11](String[6-11](state)),StoreRefNameSuffix[14-20](String[14-20](action))))))");
   }

   @Test
   public void testParseArrayIndex() throws ParserException {
      testParse(
            " this.states[5]",
            "StoreRefList[1-15](List[1-15](StoreRefExpr[1-15](String[1-5](this),List[6-15](StoreRefNameSuffix[6-12](String[6-12](states)),StoreRefNameSuffix[12-15](Seq[12-15](String[12-13]([),String[13-14](5),String[14-15](])))))))");
   }

   @Test
   public void testParseArrayRange() throws ParserException {
      testParse(
            " this.states[0..3]",
            "StoreRefList[1-18](List[1-18](StoreRefExpr[1-18](String[1-5](this),List[6-18](StoreRefNameSuffix[6-12](String[6-12](states)),StoreRefNameSuffix[12-18](Seq[12-18](String[12-13]([),Seq[13-17](String[13-14](0),String[14-16](..),String[16-17](3)),String[17-18](])))))))");
   }

   @Test
   public void testParseArrayAll() throws ParserException {
      testParse(
            " this.states[*] ",
            "StoreRefList[1-15](List[1-15](StoreRefExpr[1-15](String[1-5](this),List[6-15](StoreRefNameSuffix[6-12](String[6-12](states)),StoreRefNameSuffix[12-15](Seq[12-15](String[12-13]([),String[13-14](*),String[14-15](])))))))");
   }

   @Test
   public void testParseAllFields() throws ParserException {
      testParse(
            " this.*",
            "StoreRefList[1-7](List[1-7](StoreRefExpr[1-7](String[1-5](this),List[6-7](StoreRefNameSuffix[6-7](String[6-7](*))))))");
   }

   @Test
   public void testParseMultipleLocations() throws ParserException {
      testParse(
            " this.state, this.states[4], this.states.*",
            "StoreRefList[1-42](List[1-42](StoreRefExpr[1-11](String[1-5](this),List[6-11](StoreRefNameSuffix[6-11](String[6-11](state)))),StoreRefExpr[13-27](String[13-17](this),List[18-27](StoreRefNameSuffix[18-24](String[18-24](states)),StoreRefNameSuffix[24-27](Seq[24-27](String[24-25]([),String[25-26](4),String[26-27](]))))),StoreRefExpr[29-42](String[29-33](this),List[34-42](StoreRefNameSuffix[34-40](String[34-40](states)),StoreRefNameSuffix[41-42](String[41-42](*))))))");
   }

   @Test
   public void testParseKeywordAndLocation() {
      testWrongParse("\\nothing, state");
   }

   @Test
   public void testParseEmpty() {
      testWrongParse("     ");
   }

   @Test
   public void testParseInvalidArray() {
      testWrongParse(" this.state[ ]");
   }

   @Test
   public void testIncompleteLocation() {
      testWrongParse(" this.state. ");
   }

   private static void testWrongParse(final String text) {
      try {
         testParse(text, "");
      }
      catch (final ParserException e) {
         return;
      }
      fail("StoreRefParser parsed \"" + text + "\"");
   }

   private static void testParse(final String text, final String resultTerm)
         throws ParserException {
      final StoreRefParser parser = new StoreRefParser(
            ProfileWrapper.testProfile);
      final IASTNode result = ParserUtils.requireComplete(parser).parse(text,
            0, text.length());
      assertEquals(resultTerm, result.toString());
   }

}
