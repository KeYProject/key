package org.key_project.jmlediting.core.test.utilities;

import static org.junit.Assert.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;

public class ParserTestUtils {

   public static void testParse(final String text, final ParseFunction parser,
         final IASTNode expectedResult) throws ParserException {
      if (expectedResult == null) {
         fail("No null result can be expected");
      }
      final IASTNode parseResult = parser.parse(text, 0, text.length());
      if (parseResult == null) {
         fail("Parser returned null");
      }
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
         final ParseFunction parser) throws ParserException {
      ParserBuilder.requireComplete(parser).parse(text, 0, text.length());
   }

   public static void testParseComplete(final String text,
         final ParseFunction parser, final String resultTerm)
         throws ParserException {
      final IASTNode result = ParserBuilder.requireComplete(parser).parse(text,
            0, text.length());
      assertEquals(resultTerm, result.toString());
   }

   public static void testParsePPComplete(final String text,
         final ParseFunction parser, final String resultPPTerm)
         throws ParserException {
      final IASTNode result = ParserBuilder.requireComplete(parser).parse(text,
            0, text.length());
      assertEquals(resultPPTerm, result.prettyPrintAST());
   }

   private static void testRecovery(final String text,
         final ParseFunction parser, final Object expectedErrorNode) {
      try {
         ParserBuilder.requireComplete(parser).parse(text, 0, text.length());
         fail("Parser was able to parse");
      }
      catch (final ParserException e) {
         final IASTNode errorNode = e.getErrorNode();
         if (errorNode == null) {
            fail("Parser was unable to recover");
         }
         if (expectedErrorNode instanceof IASTNode) {
            DomCompareUtils.compareIASTNode((IASTNode) expectedErrorNode,
                  errorNode, true);
         }
         else if (expectedErrorNode instanceof String) {
            assertEquals(expectedErrorNode.toString(), errorNode.toString());
         }
         else {
            fail("Invalid comparison object");
         }
      }
   }

   public static void testRecovery(final String text,
         final ParseFunction function, final IASTNode expectedErrorNode) {
      testRecovery(text, function, (Object) expectedErrorNode);
   }

   public static void testRecovery(final String text,
         final ParseFunction function, final String expectedErrorNode) {
      testRecovery(text, function, (Object) expectedErrorNode);
   }

}
