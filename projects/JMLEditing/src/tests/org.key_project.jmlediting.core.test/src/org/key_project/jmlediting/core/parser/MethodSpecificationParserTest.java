package org.key_project.jmlediting.core.parser;

import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.IMethodSpecification;
import org.key_project.jmlediting.core.dom.Visibility;
import org.key_project.jmlediting.core.profile.IJMLProfile;

import de.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;
import static org.junit.Assert.fail;
import static org.key_project.jmlediting.core.parser.DomBuildUtils.*;

public class MethodSpecificationParserTest {

   @Test
   public void testMethodSpecification() throws ParserException {
      String string1 = "public behavior requires true; ensures false; also exceptional_behavior assignable \\nothing;";
      IMethodSpecification result1 = buildMethodSpec(
            0,
            91,
            false,
            buildBehaviorSpec(Visibility.PUBLIC, "behavior", 0, 44,
                  buildStatementSpec("requires", 16, 29, "true"),
                  buildStatementSpec("ensures", 31, 44, "false")),
            buildBehaviorSpec(Visibility.DEFAULT, "exceptional_behavior", 51,
                  91, buildStatementSpec("assignable", 72, 91, "\\nothing")));
      testMethodSpecification(string1, result1, true);

      String string2 = "@ also public normal_behavior  \n @ assignable test; \n @ \t requires x == \"hallo ; also ; \\\"\"; \n @ \t also \n ensures false; @ ensures true; \n @ also private behavior assignable x; ";
      IMethodSpecification result2 = buildMethodSpec(
            true,
            buildBehaviorSpec(
                  Visibility.PUBLIC,
                  "normal_behavior",
                  buildStatementSpec("assignable", "test"),
                  buildStatementSpec("requires", "x == \"hallo ; also ; \\\"\"")),
            buildLightweightSpec(buildStatementSpec("ensures", "false"),
                  buildStatementSpec("ensures", "true")),
            buildBehaviorSpec(Visibility.PRIVATE, "behavior",
                  buildStatementSpec("assignable", "x")));
      testMethodSpecification(string2, result2);
   }
   
   @Test
   public void testWrongMethodSpecification() {
      testWrongMethodSpecification("behavior ensures true; behavior assignable x;");
      testWrongMethodSpecification("behavior ensuresx true;");
      testWrongMethodSpecification("public normal_behavior ensures true; also");
      testWrongMethodSpecification("also ensures true; behavior ensures x;");
      testWrongMethodSpecification("protected behavior also ensures y;");
   }

   private static void testMethodSpecification(String text,
         IMethodSpecification result) throws ParserException {
      testMethodSpecification(text, result, false);
   }

   private static void testMethodSpecification(String text,
         IMethodSpecification result, boolean compareOffsets)
         throws ParserException {
      IMethodSpecification parseResult = ProfileWrapper.testProfile
            .createParser().parseMethodSpecification(text, 0, text.length(), true);
      DomCompareUtils.equalsMethodSpecification(result, parseResult,
            compareOffsets);
   }
   
   private static void testWrongMethodSpecification(String text) {
      try {
         ProfileWrapper.testProfile.createParser().parseMethodSpecification(text, 0, text.length(), true);
      } catch (ParserException e) {
         return;
      }
      fail("Parse method specification did not throw an exception");
   }

}
