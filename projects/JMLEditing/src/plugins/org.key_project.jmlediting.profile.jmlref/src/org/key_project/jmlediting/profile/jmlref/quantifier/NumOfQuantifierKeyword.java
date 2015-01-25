package org.key_project.jmlediting.profile.jmlref.quantifier;

/**
 * Implementation of the number of quantifier in JML.
 * 
 * @author Moritz Lichter
 *
 */
public class NumOfQuantifierKeyword extends AbstractQuantifierKeyword {

   /**
    * Creates a new keyword instance.
    */
   public NumOfQuantifierKeyword() {
      super("\\num_of");
   }

   @Override
   public String getDescription() {
      return "The numerical quantifier, \\num_of, returns the number of values for its variables "
            + "for which the range and the expression in its body are true. ";
   }

}
