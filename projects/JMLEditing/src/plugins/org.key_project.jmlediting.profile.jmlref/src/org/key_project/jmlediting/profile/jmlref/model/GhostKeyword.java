package org.key_project.jmlediting.profile.jmlref.model;


/**
 * The implementation of the ghost keyword.
 *
 * @author Moritz Lichter
 *
 */
public class GhostKeyword extends VariableDeclarationKeyword {

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
