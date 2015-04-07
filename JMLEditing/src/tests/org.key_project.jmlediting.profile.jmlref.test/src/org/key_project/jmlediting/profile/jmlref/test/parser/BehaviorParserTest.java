package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.testParse;
import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.testParseFail;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.test.utilities.DomBuildUtils;

public class BehaviorParserTest {

   @Test
   public void testParseBehavior1() throws ParserException {
      final String parseText1 = "behavior ensures x = y;";
      final IASTNode result1 = DomBuildUtils.buildKeywordSequence(0, 23,
            DomBuildUtils.buildKeywordSpec("behavior", 0),
            DomBuildUtils.buildKeywordSpec("ensures", 9, 23, null));
      testParse(parseText1, result1);
   }

   @Test
   public void testParseBehavior2() throws ParserException {
      final String parseText2 = "normal_behavior ensures true; requires false;  ";
      final IASTNode result2 = DomBuildUtils.buildKeywordSequence(0, 45,
            DomBuildUtils.buildKeywordSpec("normal_behavior", 0),
            DomBuildUtils.buildKeywordSpec("ensures", 16, 29, null),
            DomBuildUtils.buildKeywordSpec("requires", 30, 45, null));
      testParse(parseText2, result2);
   }

   @Test
   public void testParseWrongBehaviors1() throws ParserException {
      testParseFail("behavior esures true;");
   }

   @Test
   public void testParseWrongBehaviors2() throws ParserException {
      testParseFail("normal_behavir");
   }

   @Test
   public void testParseWrongBehaviors3() throws ParserException {
      testParseFail("nor_behavior ensures true;");
   }

}
