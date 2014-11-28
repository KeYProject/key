package org.key_project.jmlediting.core.parser;

import static org.junit.Assert.fail;
import static org.key_project.jmlediting.core.parser.DomBuildUtils.buildKeywordSequence;
import static org.key_project.jmlediting.core.parser.DomBuildUtils.buildKeywordSpec;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;

public class BehaviorParserTest {

   @Test
   public void testParseBehavior() throws ParserException {
      String parseText1 = "behavior ensures x = y;";
      IASTNode result1 = buildKeywordSequence(0,22, 
           buildKeywordSpec("behavior", 0),
           buildKeywordSpec("ensures", 9, 22, "x = y"));
      testParseBehaviorSpecification(parseText1, result1);
      String parseText2 = "normal_behavior ensures true; requires false;  ";
      IASTNode result2 = buildKeywordSequence(0, 44,
            buildKeywordSpec("normal_behavior",0),
            buildKeywordSpec("ensures", 16, 28, "true"),
            buildKeywordSpec("requires", 30, 44, "false"));
      testParseBehaviorSpecification(parseText2, result2);
   }
   
   @Test
   public void testParseWrongBehaviors() {
      testParseWrongBehaviorSpecification("behavior esures true;");
      testParseWrongBehaviorSpecification("normal_behavir");
      testParseWrongBehaviorSpecification("nor_behavior ensures true;");
   }

   private static void testParseBehaviorSpecification(String text,
         IASTNode result) throws ParserException {
      IJMLParser parser = ProfileWrapper.testProfile.createParser();
      IASTNode parseResult = parser.parse(
            text, 0, text.length());
      DomCompareUtils.compareIASTNode(result, parseResult, false);
   }

   private static void testParseWrongBehaviorSpecification(String text) {
      try {
         ProfileWrapper.testProfile.createParser().parse(
               text, 0, text.length());
      }
      catch (ParserException e) {
         return;
      }
      fail("Parsing of behavior spec did not throw an exception");
   }

}
