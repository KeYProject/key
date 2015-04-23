package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.testParseFail;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.test.utilities.ProfileWrapper;

public class SpecificationStatementParserTest {

   @Test
   public void testParseSpecificationKeyword1() throws ParserException {
      testParseSpecification("  ensures x < y; ", "ensures", "x < y", 2, 16);
   }

   @Test
   public void testParseSpecificationKeyword2() throws ParserException {
      testParseSpecification(
            "       assignable   hello ; ",
            "assignable",
            "StoreRefList[20-25](List[20-25](StoreRefExpr[20-25](StoreRefName[20-25](String[20-25](hello)),List[25-25]())))",
            7, 27);
   }

   @Test
   public void testParseSpecificationKeyword3() throws ParserException {
      testParseSpecification("ensures \"hello;\" == x;", "ensures",
            "\"hello;\" == x", 0, 22);
   }

   @Test
   public void testParseSpecificationKeyword4() throws ParserException {
      testParseSpecification("requires \"he\'llo;\" == \'\"\';", "requires",
            "\"he\'llo;\" == \'\"\'", 0, 26);
   }

   @Test
   public void testParseSpecificationKeyword5() throws ParserException {
      testParseSpecification("requires \"he\'llo\\\\;\" == \'\"\';",
            "requires", "\"he\'llo\\;\" == \'\"\'", 0, 28);
   }

   @Test
   public void testParseWrongSpecificationKeywords1() throws ParserException {
      testParseFail("  ");
   }

   @Test
   public void testParseWrongSpecificationKeywords2() throws ParserException {
      testParseFail(" ensures ");
   }

   @Test
   public void testParseWrongSpecificationKeywords3() throws ParserException {
      testParseFail(" emsures x;");
   }

   @Test
   public void testParseWrongSpecificationKeywords4() throws ParserException {
      testParseFail("ensuresx == y;");
   }

   @Test
   public void testParseWrongSpecificationKeywords5() throws ParserException {
      testParseFail("    \t ");
   }

   @Test
   public void testParseWrongSpecificationKeywords6() throws ParserException {
      testParseFail("assignable");
   }

   @Test
   public void testParseWrongSpecificationKeywords7() throws ParserException {
      testParseFail("requires x == true");
   }

   @Test
   public void testParseWrongSpecificationKeywords8() throws ParserException {
      testParseFail("");
   }

   @Test
   public void testParseWrongSpecificationKeywords9() throws ParserException {
      testParseFail("  2requires true;");

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

      assertTrue("Keyword node is not keyword", Nodes.isKeyword(keywordNode));

      assertEquals("Wrong specification keyword parsed", expectedKeyword,
            ((IKeywordNode) keywordNode).getKeywordInstance());
      assertEquals("Wrong start offset", expctedStartOffset,
            statement.getStartOffset());
      assertEquals("Wrong end offset", expectedEndOffset,
            statement.getEndOffset());
   }
}
