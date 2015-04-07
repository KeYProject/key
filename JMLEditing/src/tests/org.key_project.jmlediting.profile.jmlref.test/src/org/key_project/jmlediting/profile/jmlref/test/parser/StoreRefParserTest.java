package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.utilities.ParserTestUtils;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefListParser;
import org.key_project.jmlediting.profile.jmlref.test.utilities.ProfileWrapper;

public class StoreRefParserTest {

   protected ParseFunction createParser(final boolean allowInformal) {
      return new StoreRefListParser(ProfileWrapper.testProfile, allowInformal);
   }

   @Test
   public void testParseNothingKeyword() throws ParserException {
      this.testParse(" \\nothing", "StoreRefList[1-9](Keyword[1-9](\\nothing))");
   }

   @Test
   public void testEverythingKeyword() throws ParserException {
      this.testParse("\t \\everything  ",
            "StoreRefList[2-13](Keyword[2-13](\\everything))");
   }

   @Test
   public void testParseSimpleIdentifier() throws ParserException {
      this.testParse(
            " state ",
            "StoreRefList[1-6](List[1-6](StoreRefExpr[1-6](StoreRefName[1-6](String[1-6](state)),List[6-6]())))");
   }

   @Test
   public void testParseQualifiedIdentifier() throws ParserException {
      this.testParse(
            " this.state . action",
            "StoreRefList[1-20](List[1-20](StoreRefExpr[1-20](StoreRefName[1-5](String[1-5](this)),List[6-20](StoreRefNameSuffix[6-11](String[6-11](state)),StoreRefNameSuffix[14-20](String[14-20](action))))))");
   }

   @Test
   public void testParseQualifiedRecovery() throws ParserException {
      this.testRecovery(
            " this.state. ",
            "StoreRefList[1-12](List[1-12](StoreRefExpr[1-12](StoreRefName[1-5](String[1-5](this)),List[6-12](StoreRefNameSuffix[6-11](String[6-11](state)),StoreRefNameSuffix[11-12](ErrorNode[11-12](String[11-12](.)))))))");
   }

   @Test
   public void testParseArrayIndex() throws ParserException {
      this.testParse(
            " this.states[5]",
            "StoreRefList[1-15](List[1-15](StoreRefExpr[1-15](StoreRefName[1-5](String[1-5](this)),List[6-15](StoreRefNameSuffix[6-12](String[6-12](states)),StoreRefNameSuffix[12-15](Seq[12-15](String[12-13]([),Primary[13-14](IntegerLiteral[13-14](String[13-14](5))),String[14-15](])))))))");
   }

   @Test
   public void testParseArrayRange() throws ParserException {
      this.testParse(
            " this.states[0..3]",
            "StoreRefList[1-18](List[1-18](StoreRefExpr[1-18](StoreRefName[1-5](String[1-5](this)),List[6-18](StoreRefNameSuffix[6-12](String[6-12](states)),StoreRefNameSuffix[12-18](Seq[12-18](String[12-13]([),Seq[13-17](Primary[13-14](IntegerLiteral[13-14](String[13-14](0))),String[14-16](..),Primary[16-17](IntegerLiteral[16-17](String[16-17](3)))),String[17-18](])))))))");
   }

   @Test
   public void testParseArrayAll() throws ParserException {
      this.testParse(
            " this.states[*] ",
            "StoreRefList[1-15](List[1-15](StoreRefExpr[1-15](StoreRefName[1-5](String[1-5](this)),List[6-15](StoreRefNameSuffix[6-12](String[6-12](states)),StoreRefNameSuffix[12-15](Seq[12-15](String[12-13]([),String[13-14](*),String[14-15](])))))))");
   }

   @Test
   public void testParseArrayWithExpression() throws ParserException {
      this.testParse(
            "this.states[hello.get() - 3]",
            "StoreRefList[0-28](List[0-28](StoreRefExpr[0-28](StoreRefName[0-4](String[0-4](this)),List[5-28](StoreRefNameSuffix[5-11](String[5-11](states)),StoreRefNameSuffix[11-28](Seq[11-28](String[11-12]([),Additive[12-27](Primary[12-23](Identifier[12-17](String[12-17](hello)),List[17-23](MemberAccess[17-21](String[17-18](.),String[18-21](get)),MethodCall[21-23](None[21-23]()))),String[24-25](-),Primary[26-27](IntegerLiteral[26-27](String[26-27](3)))),String[27-28](])))))))");
   }

   @Test
   public void testParseAllFields() throws ParserException {
      this.testParse(
            " this.*",
            "StoreRefList[1-7](List[1-7](StoreRefExpr[1-7](StoreRefName[1-5](String[1-5](this)),List[6-7](StoreRefNameSuffix[6-7](String[6-7](*))))))");
   }

   @Test
   public void testParseMultipleLocations() throws ParserException {
      this.testParse(
            " this.state, this.states[4], this.states.*",
            "StoreRefList[1-42](List[1-42](StoreRefExpr[1-11](StoreRefName[1-5](String[1-5](this)),List[6-11](StoreRefNameSuffix[6-11](String[6-11](state)))),StoreRefExpr[13-27](StoreRefName[13-17](String[13-17](this)),List[18-27](StoreRefNameSuffix[18-24](String[18-24](states)),StoreRefNameSuffix[24-27](Seq[24-27](String[24-25]([),Primary[25-26](IntegerLiteral[25-26](String[25-26](4))),String[26-27](]))))),StoreRefExpr[29-42](StoreRefName[29-33](String[29-33](this)),List[34-42](StoreRefNameSuffix[34-40](String[34-40](states)),StoreRefNameSuffix[41-42](String[41-42](*))))))");
   }

   @Test
   public void testParseInformalDescription() throws ParserException {
      this.testParse(
            "  (* Mein Name ist Hase *)  ",
            "StoreRefList[2-26](List[2-26](InformalDescription[2-26](String[4-24]( Mein Name ist Hase ))))");
   }

   @Test
   public void testParseKeywordAndLocation() {
      this.testWrongParse("\\nothing, state");
   }

   @Test
   public void testParseEmpty() {
      this.testWrongParse("     ");
   }

   @Test
   public void testParseInvalidArray() {
      this.testWrongParse(" this.state[ ]");
   }

   @Test
   public void testIncompleteLocation() {
      this.testWrongParse(" this.state. ");
   }

   @Test
   public void testNoInformalDescription() {
      this.testWrongParse(" (* hello *) ", false);
   }

   protected void testWrongParse(final String text) {
      this.testWrongParse(text, true);
   }

   protected void testWrongParse(final String text,
         final boolean allowInformalDescr) {
      try {
         this.testParse(text, "", allowInformalDescr);
      }
      catch (final ParserException e) {
         return;
      }
      fail("StoreRefParser parsed \"" + text + "\"");
   }

   private void testRecovery(final String text, final String recoveryTerm) {
      ParserTestUtils.testRecovery(text, this.createParser(true), recoveryTerm);
   }

   private void testParse(final String text, final String resultTerm)
         throws ParserException {
      this.testParse(text, resultTerm, true);
   }

   private void testParse(final String text, final String resultTerm,
         final boolean allowInformalDescr) throws ParserException {
      ParserTestUtils.testParseComplete(text,
            this.createParser(allowInformalDescr), resultTerm);
   }

}
