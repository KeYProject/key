package org.key_project.jmlediting.core.parser;

import static org.junit.Assert.assertTrue;

import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.IBehaviorSpecification;
import org.key_project.jmlediting.core.dom.Visibility;
import org.key_project.jmlediting.core.profile.IJMLProfile;

import de.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;

public class BehaviorParserTest {

   @Test
   public void testParseBehavior() throws ParserException {
      String parseText1 = "behavior ensures x = y;";
      IBehaviorSpecification result1 = DomBuildUtils.buildBehaviorSpec(Visibility.DEFAULT,
            "behavior", 0, 22, DomBuildUtils.buildStatementSpec("ensures", 9, 22, "x = y"));
      testParseBehaviorSpecification(parseText1, result1);
      String parseText2 = "normal_behavior ensures true; requires false;  ";
      IBehaviorSpecification result2 = DomBuildUtils.buildBehaviorSpec(Visibility.DEFAULT,
            "normal_behavior", 0, 44,
            DomBuildUtils.buildStatementSpec("ensures", 16, 28, "true"),
            DomBuildUtils.buildStatementSpec("requires", 30, 44, "false"));
      testParseBehaviorSpecification(parseText2, result2);
   }
   
   @Test
   public void testParseBehaviorWithVisibility() throws ParserException {
      String parseText1 = " public behavior @ assignable z;  ";
      IBehaviorSpecification result1 = DomBuildUtils.buildBehaviorSpec(Visibility.PUBLIC,
            "behavior", 1, 31, DomBuildUtils.buildStatementSpec("assignable", 19, 31, "z"));
      testParseBehaviorSpecification(parseText1, result1);
      String parseText2 = "protected exceptional_behavior";
      IBehaviorSpecification result2 = DomBuildUtils.buildBehaviorSpec(Visibility.PROTECTED,
            "exceptional_behavior", 0, 29);
      testParseBehaviorSpecification(parseText2, result2);
   }

   private static void testParseBehaviorSpecification(String text,
         IBehaviorSpecification result) throws ParserException {
      IJMLParser parser = ProfileWrapper.testProfile.createParser();
      IBehaviorSpecification parseResult = parser.parseBehaviorSpecification(
            text, 0, text.length());
      DomCompareUtils.equalsBehaviorSpecification(result, parseResult, false);
   }

}
