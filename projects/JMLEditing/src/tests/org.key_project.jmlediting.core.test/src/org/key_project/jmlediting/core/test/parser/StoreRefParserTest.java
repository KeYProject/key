package org.key_project.jmlediting.core.test.parser;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.ParserUtils;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefParser;

public class StoreRefParserTest {

   @Test
   public void testParseNothingKeyword() throws ParserException {
      testParse(" \\nothing");
   }

   @Test
   public void testEverythingKeyword() throws ParserException {
      testParse("\t \\everything  ");
   }

   @Test
   public void testParseSimpleIdentifier() throws ParserException {
      testParse(" state ");
   }

   @Test
   public void testParseQualifiedIdentifier() throws ParserException {
      testParse(" this.state . action");
   }

   @Test
   public void testParseArrayIndex() throws ParserException {
      testParse(" this.states[5]");
   }

   @Test
   public void testParseArrayRange() throws ParserException {
      testParse(" this.states[0..3]");
   }

   @Test
   public void testParseArrayAll() throws ParserException {
      testParse(" this.states[*] ");
   }

   @Test
   public void testParseAllFields() throws ParserException {
      testParse(" this.*");
   }

   private static void testParse(final String text) throws ParserException {
      final StoreRefParser parser = new StoreRefParser(
            ProfileWrapper.testProfile);
      System.out.println(ParserUtils.requireComplete(parser).parse(text, 0,
            text.length()));
   }

}
