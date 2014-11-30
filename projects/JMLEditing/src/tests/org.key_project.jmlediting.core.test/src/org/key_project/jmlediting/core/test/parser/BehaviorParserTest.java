package org.key_project.jmlediting.core.test.parser;

import static org.key_project.jmlediting.core.test.parser.DomBuildUtils.buildKeywordSequence;
import static org.key_project.jmlediting.core.test.parser.DomBuildUtils.buildKeywordSpec;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;

public class BehaviorParserTest {

   @Test
   public void testParseBehavior1() throws ParserException {
      final String parseText1 = "behavior ensures x = y;";
      final IASTNode result1 = buildKeywordSequence(0, 22,
            buildKeywordSpec("behavior", 0),
            buildKeywordSpec("ensures", 9, 22, "x = y"));
      testParseBehaviorSpecification(parseText1, result1);
   }

   @Test
   public void testParseBehavior2() throws ParserException {
      final String parseText2 = "normal_behavior ensures true; requires false;  ";
      final IASTNode result2 = buildKeywordSequence(0, 44,
            buildKeywordSpec("normal_behavior", 0),
            buildKeywordSpec("ensures", 16, 28, "true"),
            buildKeywordSpec("requires", 30, 44, "false"));
      testParseBehaviorSpecification(parseText2, result2);
   }

   @Test(expected = ParserException.class)
   public void testParseWrongBehaviors1() throws ParserException {
      testParseBehaviorSpecification("behavior esures true;");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongBehaviors2() throws ParserException {
      testParseBehaviorSpecification("normal_behavir");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongBehaviors3() throws ParserException {
      testParseBehaviorSpecification("nor_behavior ensures true;");
   }

   private static void testParseBehaviorSpecification(final String text)
         throws ParserException {
      testParseBehaviorSpecification(text, null);
   }

   private static void testParseBehaviorSpecification(final String text,
         final IASTNode result) throws ParserException {
      final IJMLParser parser = ProfileWrapper.testProfile.createParser();
      final IASTNode parseResult = parser.parse(text, 0, text.length());
      DomCompareUtils.compareIASTNode(result, parseResult, false);
   }

}
