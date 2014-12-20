package org.key_project.jmlediting.profile.jmlref.visibility;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

public abstract class JMLVisibilityKeyword extends AbstractEmptyKeyword
      implements IToplevelKeyword {

   public JMLVisibilityKeyword(final String keyword) {
      super(keyword);
   }

}
