package org.key_project.jmlediting.core.profile;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class JMLProfileHelper {

   public static IKeyword findKeyword(final IJMLProfile profile,
         final String keyword) {
      return findKeyword(profile.getSupportedKeywords(), keyword);
   }

   public static IKeyword findKeyword(
         final Iterable<? extends IKeyword> keywords, final String keyword) {
      IKeyword foundKeyword = null;
      for (final IKeyword availableKeyword : keywords) {
         if (availableKeyword.getKeywords().contains(keyword)) {
            foundKeyword = availableKeyword;
            break;
         }
      }
      return foundKeyword;
   }

}
