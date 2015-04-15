package org.key_project.jmlediting.profile.key.test.utilities;

import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.test.utilities.ParserTestUtils;
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;
import org.key_project.jmlediting.profile.key.KeYProfile;

public class JMLEditingKeYProfileTestUtils {

   private static JMLReferenceProfile keyProfile = new KeYProfile();

   public static JMLReferenceProfile keyProfile() {
      return keyProfile;
   }

   public static void testParseComplete(final String text)
         throws ParserException {
      ParserTestUtils.testParseComplete(text, keyProfile().createParser());
   }

}
