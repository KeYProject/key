package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.key_project.jmlediting.profile.jmlref.test.utilities.JMLRefParserTestUtils.testRecovery;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class ParserRecoveryTest {

   @Test
   public void testRecoveryFromWrongKeywordContent() throws ParserException {
      testRecovery(
            "assignable 123; also",
            "Node[0-20](KeywordAppl[0-11](Keyword[0-10](assignable),ErrorNode[10-10]()),ErrorNode[11-16](UnparsedText[11-16](123; )),Keyword[16-20](also))");
   }

   @Test
   public void testRecoveryFromWrongToplevelKeyword() {
      testRecovery(
            "publik behavior",
            "Node[0-15](ErrorNode[0-7](UnparsedText[0-7](publik )),Keyword[7-15](behavior))");
   }
}
