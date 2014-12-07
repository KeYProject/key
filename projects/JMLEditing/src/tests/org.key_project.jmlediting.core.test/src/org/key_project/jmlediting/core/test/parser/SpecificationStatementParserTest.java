package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;

public class SpecificationStatementParserTest {

   @Test
   public void testParseSpecificationKeyword1() throws ParserException {
      testParseSpecification("  ensures x < y; ", "ensures", "x < y", 2, 16);
   }

   @Test
   public void testParseSpecificationKeyword2() throws ParserException {
      testParseSpecification("       assignable   hello ; ", "assignable",
            "  hello ", 7, 27);
   }

   @Test
   public void testParseSpecificationKeyword3() throws ParserException {
      testParseSpecification("ensures \"hello;\" == x;", "ensures",
            "\"hello;\" == x", 0, 22);
   }

   @Test
   public void testParseSpecificationKeyword4() throws ParserException {
      testParseSpecification("requires \"he\'llo;\" == \'\";\';", "requires",
            "\"he\'llo;\" == \'\";\'", 0, 27);
   }

   @Test
   public void testParseSpecificationKeyword5() throws ParserException {
      testParseSpecification("requires \"he\'llo\\;\" == \'\";\';", "requires",
            "\"he\'llo\\;\" == \'\";\'", 0, 28);
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords1() throws ParserException {
      testParseWrongSpecification("  ");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords2() throws ParserException {
      testParseWrongSpecification(" ensures ");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords3() throws ParserException {
      testParseWrongSpecification(" emsures x;");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords4() throws ParserException {
      testParseWrongSpecification("ensuresx == y;");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords5() throws ParserException {
      testParseWrongSpecification("    \t ");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords6() throws ParserException {
      testParseWrongSpecification("assignable");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords7() throws ParserException {
      testParseWrongSpecification("requires x == true");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords8() throws ParserException {
      testParseWrongSpecification("");
   }

   @Test(expected = ParserException.class)
   public void testParseWrongSpecificationKeywords9() throws ParserException {
      testParseWrongSpecification("  2requires true;");

   }

   private static void testParseSpecification(final String specText,
         final String expectedKeyword, final String expectedContent,
         final int expctedStartOffset, final int expectedEndOffset)
               throws ParserException {
      final IJMLParser parser = ProfileWrapper.testProfile.createParser();

      final IASTNode statement = parser.parse(specText, 0, specText.length());
      assertEquals("More than one keyword parsed", 1, statement.getChildren()
            .size());

      final IASTNode keywordNode = statement.getChildren().get(0).getChildren()
            .get(0);
      final IASTNode keywordContentNode = statement.getChildren().get(0)
            .getChildren().get(1);
      final IASTNode stringNode = keywordContentNode.getChildren().get(0);

      assertTrue("Keyword node is not keyword", Nodes.isKeyword(keywordNode));
      assertTrue("Content is not string", Nodes.isString(stringNode));

      assertEquals("Wrong specification keyword parsed", expectedKeyword,
            ((IKeywordNode) keywordNode).getKeywordInstance());
      assertEquals("Wrong content", expectedContent,
            ((IStringNode) stringNode).getString());
      assertEquals("Wrong start offset", expctedStartOffset,
            statement.getStartOffset());
      assertEquals("Wrong end offset", expectedEndOffset,
            statement.getEndOffset());
   }

   private static void testParseWrongSpecification(final String specText)
         throws ParserException {

      ProfileWrapper.testProfile.createParser().parse(specText, 0,
            specText.length());

   }
}
