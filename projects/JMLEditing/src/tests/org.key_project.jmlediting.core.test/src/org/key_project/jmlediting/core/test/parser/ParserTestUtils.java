package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;

public class ParserTestUtils {

   public static void testParse(final String content,
         final IASTNode expectedResult) throws ParserException {
      final IASTNode result = ProfileWrapper.testProfile.createParser().parse(
            content, 0, content.length());
      DomCompareUtils.compareIASTNode(expectedResult, result, true);
   }

   public static void testParseFail(final String content)
         throws ParserException {
      try {
         testParse(content, null);
      }
      catch (final ParserException e) {
         return;
      }
      fail("Expected a parsing error");
   }

   public static void testParse(final String text, final ParseFunction parser,
         final IASTNode expectedResult) throws ParserException {
      final IASTNode parseResult = parser.parse(text, 0, text.length());
      DomCompareUtils.compareIASTNode(expectedResult, parseResult, true);
   }

   public static void testParseFail(final String text,
         final ParseFunction parser) {
      try {
         parser.parse(text, 0, text.length());
      }
      catch (final ParserException e) {
         return;
      }
      fail("Expected a parsing error");
   }

   public static void testParseComplete(final String text,
         final ParseFunction parser, final String resultTerm)
               throws ParserException {
      final IASTNode result = ParserBuilder.requireComplete(parser).parse(text,
            0, text.length());
      assertEquals(resultTerm, result.toString());
   }

}
