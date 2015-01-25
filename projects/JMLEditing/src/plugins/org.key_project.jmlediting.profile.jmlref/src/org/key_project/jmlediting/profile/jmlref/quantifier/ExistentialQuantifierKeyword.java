package org.key_project.jmlediting.profile.jmlref.quantifier;

/**
 * Implementation of the existential quantifier.
 *
 * @author Moritz Lichter
 *
 */
public class ExistentialQuantifierKeyword extends AbstractQuantifierKeyword {

   /**
    * Creates a new instance for this keyword.
    */
   public ExistentialQuantifierKeyword() {
      super("\\exists");
   }

   @Override
   public String getDescription() {
      return "The quantifier \\exists is the existential quantifier.";
   }

}
