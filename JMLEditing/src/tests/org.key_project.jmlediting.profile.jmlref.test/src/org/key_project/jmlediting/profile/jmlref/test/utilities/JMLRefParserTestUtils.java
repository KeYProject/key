package org.key_project.jmlediting.profile.jmlref.test.utilities;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.utilities.ParserTestUtils;

public class JMLRefParserTestUtils {

   public static void testParse(final String content,
         final IASTNode expectedResult) throws ParserException {
      ParserTestUtils.testParse(content,
            ProfileWrapper.testProfile.createParser(), expectedResult);
   }

   public static void testParseFail(final String content) {
      ParserTestUtils.testParseFail(content,
            ProfileWrapper.testProfile.createParser());
   }

   public static void testRecovery(final String text,
         final IASTNode expectedErrorNode) {
      ParserTestUtils.testRecovery(text,
            ProfileWrapper.testProfile.createParser(), expectedErrorNode);
   }

   public static void testParseComplete(final String text)
         throws ParserException {
      ParserTestUtils.testParseComplete(text,
            ProfileWrapper.testProfile.createParser());
   }

   public static void testParsePPComplete(final String text,
         final String expected) throws ParserException {
      ParserTestUtils.testParsePPComplete(text,
            ProfileWrapper.testProfile.createParser(), expected);
   }

   public static void testRecovery(final String text,
         final String expectedErrorNode) {
      ParserTestUtils.testRecovery(text,
            ProfileWrapper.testProfile.createParser(), expectedErrorNode);
   }

}
