package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

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

   /**
    * Get a filtered set of {@link IKeyword}, e.g. to propose only a subset of
    * {@link IKeyword}
    *
    * @param profile
    *           the {@link IJMLProfile} to get the {@link IKeyword} from
    * @param clazz
    *           the Class extending from {@link IKeyword} to filter
    * @return the filtered Set of {@link IKeyword} all Assignable from clazz
    */
   public static Set<IKeyword> filterKeywords(final IJMLProfile profile,
         final Class<? extends IKeyword> clazz) {
      final Set<IKeyword> result = new HashSet<IKeyword>();
      for (final IKeyword container : profile.getSupportedKeywords()) {
         if (clazz.isAssignableFrom(container.getClass())) {
            result.add(container);
         }
      }
      return Collections.unmodifiableSet(result);
   }
}
