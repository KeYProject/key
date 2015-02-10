package org.key_project.jmlediting.profile.key.test.other;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.test.parser.InvariantForTest;
import org.key_project.jmlediting.profile.key.test.KeyProfileTestUtils;

public class KeyInvariantTest extends InvariantForTest {

   @Override
   protected ParseFunction createParser() {
      return KeyProfileTestUtils.keyProfile().createParser();
   }

   @Test
   public void testInvInExpression() {
      this.testParse("requires a && (b.get().x.\\inv || a);");
   }

   @Test
   public void testInvToplevel() {
      this.testParse("requires b && \\inv || a.\\inv; ");
   }

}
