package org.key_project.jmlediting.profile.jmlref.test.parser;

import static org.junit.Assert.fail;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.utilities.ParserTestUtils;
import org.key_project.jmlediting.profile.jmlref.test.utilities.ProfileWrapper;

public class InvariantForTest {

   protected ParseFunction createParser() {
      return ProfileWrapper.testProfile.createParser();
   }

   @Test
   public void testInvariantForInRequires() {
      this.testParse("requires invariant_for(x.get()) && b;");
   }

   @Test
   public void testInvariantForInEnsures() {
      this.testParse("ensures x <==> (a || invariant_for(Static.getMember()[Math.rand()]));");
   }

   protected void testParse(final String text) {
      try {
         ParserTestUtils.testParseComplete(text, this.createParser());
      }
      catch (final ParserException e) {
         fail(e.getMessage());
      }
   }

}
