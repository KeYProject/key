package org.key_project.jmlediting.profile.jmlref.quantifier;

/**
 * Implementation of the forall quantifier of JML.
 * 
 * @author Moritz Lichter
 *
 */
public class ForallQuantifierKeyword extends AbstractQuantifierKeyword {

   /**
    * New instance of the keyword.
    */
   public ForallQuantifierKeyword() {
      super("\\forall");
   }

   @Override
   public String getDescription() {
      return "The quantifier \\forall is the universal quantifier.";
   }

}
