package org.key_project.jmlediting.profile.jmlref.model;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

public class GhostKeyword extends AbstractEmptyKeyword implements
      IToplevelKeyword {

   public GhostKeyword() {
      super("ghost");
   }

   @Override
   public String getDescription() {
      return "The ghost modifier introduces a specification-only field that "
            + "is maintained by special set statements";
   }

}
