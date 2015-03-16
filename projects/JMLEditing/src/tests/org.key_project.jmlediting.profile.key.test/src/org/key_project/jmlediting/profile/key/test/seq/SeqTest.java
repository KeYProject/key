package org.key_project.jmlediting.profile.key.test.seq;

import static org.key_project.jmlediting.core.test.parser.ParserTestUtils.testParseComplete;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.key.test.KeyProfileTestUtils;

public class SeqTest {

   @Test
   public void testGhostSet() throws ParserException {
      testParseComplete("ghost \\seq visited = \\seq_empty;",
            KeyProfileTestUtils.keyProfile().createParser());
   }

}
