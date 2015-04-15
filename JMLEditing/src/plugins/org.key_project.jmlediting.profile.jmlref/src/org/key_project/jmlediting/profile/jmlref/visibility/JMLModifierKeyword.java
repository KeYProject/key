package org.key_project.jmlediting.profile.jmlref.visibility;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyToplevelKeyword;

/**
 * Base class for all visibility keywords which are special to JML.
 *
 * @author Moritz Lichter
 *
 */
public abstract class JMLModifierKeyword extends AbstractEmptyToplevelKeyword {

   /**
    * Creates a new keyword instance.
    *
    * @param keyword
    *           the keyword
    */
   public JMLModifierKeyword(final String keyword) {
      super(keyword);
   }

}
