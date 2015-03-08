package org.key_project.jmlediting.profile.jmlref.visibility;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyToplevelKeyword;

/**
 * Base class for all Java visibility keywords (which are not special to JML).
 *
 * @author Moritz Lichter
 *
 */
public abstract class JavaModifierKeyword extends AbstractEmptyToplevelKeyword {

   /**
    * Creates a new keyword instance.
    *
    * @param keyword
    *           the keyword
    */
   public JavaModifierKeyword(final String keyword) {
      super(keyword);
   }

   @Override
   public String getDescription() {
      // For java keywords we do not need a description because any developer
      // should be familiar with them
      return null;
   }

}
