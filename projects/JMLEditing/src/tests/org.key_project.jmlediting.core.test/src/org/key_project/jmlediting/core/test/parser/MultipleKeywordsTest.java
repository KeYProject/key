package org.key_project.jmlediting.core.test.parser;

import static org.key_project.jmlediting.core.test.parser.ParserTestUtils.*;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;

public class MultipleKeywordsTest {

   @Test
   public void parseMultipleKeywordsTest1() throws ParserException {
      final String content = "behavior\n\t @ assignable x;";
      final IASTNode expectedResult = DomBuildUtils.buildKeywordSequence(0, 26,
            DomBuildUtils.buildKeywordSpec("behavior", 0),
            DomBuildUtils.buildKeywordSpec("assignable", 13, 26, "x"));
      testParse(content, expectedResult);
   }

   @Test
   public void parseMultipleKeywordsTest2() throws ParserException {
      final String content = "  normal_behavior \n@\t requires   x == 1; \n@\t assignable y; \n@ exceptional_behavior \n@\tensures false;  ";
      final IASTNode expectedResult = DomBuildUtils.buildKeywordSequence(2,
            100, DomBuildUtils.buildKeywordSpec("normal_behavior", 2),
            DomBuildUtils.buildKeywordSpec("requires", 22, 40, "  x == 1"),
            DomBuildUtils.buildKeywordSpec("assignable", 45, 58, "y"),
            DomBuildUtils.buildKeywordSpec("exceptional_behavior", 63),
            DomBuildUtils.buildKeywordSpec("ensures", 86, 100, "false"));
      testParse(content, expectedResult);
   }

   @Test
   public void parseWrongMultipleKeywords1() throws ParserException {
      testParseFail(" @ normal_behavior");
   }

   @Test
   public void parseWrongMultipleKeywords2() throws ParserException {
      testParseFail("behavior ensures x normal_behavior");
   }

   @Test
   public void parseWrongMultipleKeywords3() throws ParserException {
      testParseFail(" \n @");
   }

}
