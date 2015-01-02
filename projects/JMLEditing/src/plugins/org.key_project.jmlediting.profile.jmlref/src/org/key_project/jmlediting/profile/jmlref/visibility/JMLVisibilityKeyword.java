package org.key_project.jmlediting.profile.jmlref.visibility;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

/**
 * Base class for all visibility keywords which are special to JML.
 *
 * @author Moritz Lichter
 *
 */
public abstract class JMLVisibilityKeyword extends AbstractEmptyKeyword
implements IToplevelKeyword {

   /**
    * Creates a new keyword instance.
    * 
    * @param keyword
    *           the keyword
    */
   public JMLVisibilityKeyword(final String keyword) {
      super(keyword);
   }

}
