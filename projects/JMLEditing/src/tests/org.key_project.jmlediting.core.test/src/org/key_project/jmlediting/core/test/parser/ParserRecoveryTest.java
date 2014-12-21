package org.key_project.jmlediting.core.test.parser;

import static org.key_project.jmlediting.core.test.parser.ParserTestUtils.testRecovery;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;

public class ParserRecoveryTest {

   @Test
   public void testRecoveryFromWrongKeywordContent() throws ParserException {
      testRecovery(
            "assignable 123; also",
            "Node[0-20](KeywordAppl[0-10](Keyword[0-10](assignable),ErrorNode[10-10]()),ErrorNode[11-15](UnparsedText[11-15](123;)),Keyword[16-20](also))");
   }

   @Test
   public void testRecoveryFromWrongToplevelKeyword() {
      testRecovery("publik behavior",
            "Node[0-15](ErrorNode[0-6](UnparsedText[0-6](publik)),Keyword[7-15](behavior))");
   }

}
