package org.key_project.jmlediting.core.test.parser;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;

public class MultipleKeywordsTest {

   @Test
   public void parseMultipleKeywordsTest1() throws ParserException {
      final String content = "behavior \n @ assignable x;";
      final IASTNode expectedResult = DomBuildUtils.buildKeywordSequence(0, 25,
            DomBuildUtils.buildKeywordSpec("behavior", 0),
            DomBuildUtils.buildKeywordSpec("assignable", 13, 25, "x"));
      testParseMultipleKeywords(content, expectedResult);
   }

   @Test
   public void parseMultipleKeywordsTest2() throws ParserException {
      final String content = "  normal_behavior \n@\t requires   x == 1; \n@\t assignable y; \n@ exceptional_behavior \n@\tensures false;  ";
      final IASTNode expectedResult = DomBuildUtils.buildKeywordSequence(2, 99,
            DomBuildUtils.buildKeywordSpec("normal_behavior", 2),
            DomBuildUtils.buildKeywordSpec("requires", 22, 39, "  x == 1"),
            DomBuildUtils.buildKeywordSpec("assignable", 45, 57, "y"),
            DomBuildUtils.buildKeywordSpec("exceptional_behavior", 62),
            DomBuildUtils.buildKeywordSpec("ensures", 86, 99, "false"));
      testParseMultipleKeywords(content, expectedResult);
   }

   @Test(expected = ParserException.class)
   public void parseWrongMultipleKeywords1() throws ParserException {
      testParseMultipleKeywords(" @ normal_behavior");
   }

   @Test(expected = ParserException.class)
   public void parseWrongMultipleKeywords2() throws ParserException {
      testParseMultipleKeywords("behavior ensures x normal_behavior");
   }

   @Test(expected = ParserException.class)
   public void parseWrongMultipleKeywords3() throws ParserException {
      testParseMultipleKeywords(" \n @");
   }

   private static void testParseMultipleKeywords(final String content)
         throws ParserException {
      testParseMultipleKeywords(content, null);
   }

   private static void testParseMultipleKeywords(final String content,
         final IASTNode expectedResult) throws ParserException {
      final IASTNode result = ProfileWrapper.testProfile.createParser().parse(
            content, 0, content.length());
      DomCompareUtils.compareIASTNode(expectedResult, result, true);
   }
}
