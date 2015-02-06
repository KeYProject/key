package org.key_project.jmlediting.profile.jmlref.model;

import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

/**
 * The implementation of the ghost keyword.
 *
 * @author Moritz Lichter
 *
 */
public class GhostKeyword extends VariableDeclarationKeyword implements
      IToplevelKeyword {

   /**
    * Creates a new instance of this keyword.
    */
   public GhostKeyword() {
      super("ghost");
   }

   @Override
   public String getDescription() {
      return "The ghost modifier introduces a specification-only field that "
            + "is maintained by special set statements";
   }

}
