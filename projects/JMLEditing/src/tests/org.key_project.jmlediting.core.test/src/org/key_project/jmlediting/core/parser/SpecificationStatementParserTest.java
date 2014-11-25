package org.key_project.jmlediting.core.parser;

import static org.junit.Assert.*;

import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.ISpecificationStatement;
import org.key_project.jmlediting.core.profile.IJMLProfile;

import de.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;

public class SpecificationStatementParserTest {

   @Test
   public void testParseSpecificationKeyword() throws ParserException {
      testParseSpecification("  ensures x < y; ", "ensures", "x < y", 2, 15);
      testParseSpecification("       assignable   hello ; ", "assignable" ,"  hello ", 7, 26);
      testParseSpecification("ensures \"hello;\" == x;", "ensures", "\"hello;\" == x", 0, 21);
      testParseSpecification("requires \"he\'llo;\" == \'\";\';", "requires", "\"he\'llo;\" == \'\";\'", 0, 26);
      testParseSpecification("requires \"he\'llo\\;\" == \'\";\';", "requires", "\"he\'llo\\;\" == \'\";\'", 0, 27);
   }
   
   @Test
   public void testParseWrongSpecificationKeywords() {
      testParseWrongSpecification(" ensures ");
      testParseWrongSpecification(" emsures x;");
      testParseWrongSpecification("ensuresx == y;");
      testParseWrongSpecification("    \t ");
      testParseWrongSpecification("assignable");
      testParseWrongSpecification("requires x == true");
      testParseWrongSpecification("");
      testParseWrongSpecification("  2requires true;");
      
   }
   
   private void testParseSpecification(String specText, String expectedKeyword, String expectedContent, int expctedStartOffset, int expectedEndOffset) throws ParserException {
      IJMLParser parser = ProfileWrapper.testProfile.createParser();
      
     
      ISpecificationStatement statement = parser.parseSpecificationStatement(specText, 0, specText.length());
      
      assertEquals("Wrong specification keyword parsed", expectedKeyword, statement.getKeyword().getKeyword());
      assertEquals("Wrong content", expectedContent, statement.getContent());
      assertEquals("Wrong start offset", expctedStartOffset, statement.getStartOffset());
      assertEquals("Wrong end offset", expectedEndOffset, statement.getEndOffset());
   }
   
   private void testParseWrongSpecification(String specText) {
      try {
         ProfileWrapper.testProfile.createParser().parseSpecificationStatement(specText, 0, specText.length());
      } catch (ParserException e) {
         return;
      }
      fail("Parse specification did not encountered an exception");
   }
}
