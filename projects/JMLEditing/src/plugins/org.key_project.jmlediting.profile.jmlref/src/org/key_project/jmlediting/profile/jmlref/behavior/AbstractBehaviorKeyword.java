package org.key_project.jmlediting.profile.jmlref.behavior;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

public abstract class AbstractBehaviorKeyword extends AbstractEmptyKeyword
      implements IToplevelKeyword {

   public AbstractBehaviorKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

}
