package org.key_project.jmlediting.profile.jmlref.model;


/**
 * The implementation of the model keyword.
 *
 * @author Moritz Lichter
 *
 */
public class ModelKeyword extends VariableDeclarationKeyword {

   /**
    * Creates a new instance of model.
    */
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
