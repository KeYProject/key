package org.key_project.jmlediting.profile.jmlref.model;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

public class ModelKeyword extends AbstractEmptyKeyword implements
      IToplevelKeyword {

   public ModelKeyword() {
      super("model");
   }

   @Override
   public String getDescription() {
      return "The model modifier introduces a specification-only feature. "
            + "For fields it also has a special meaning, which is that the "
            + "field can be represented by concrete fields";
   }

}
