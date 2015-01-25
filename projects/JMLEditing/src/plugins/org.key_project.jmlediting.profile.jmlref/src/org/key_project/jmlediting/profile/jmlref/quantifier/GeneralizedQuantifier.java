package org.key_project.jmlediting.profile.jmlref.quantifier;

/**
 * The {@link GeneralizedQuantifier} is the superclass for the numerical
 * quantifiers to share the common description.
 *
 * @author Moritz Lichter
 *
 */
public class GeneralizedQuantifier extends AbstractQuantifierKeyword {

   /**
    * Create a new {@link GeneralizedQuantifier} with the given keyword.
    * 
    * @param keyword
    *           the keyword of the quantifier
    */
   public GeneralizedQuantifier(final String keyword) {
      super(keyword);
   }

   @Override
   public String getDescription() {
      return "The quantifiers \\max, \\min, \\product, and \\sum, are generalized quantifiers "
            + "that return the maximum, minimum, product, or sum of the values of the "
            + "expressions given, where the variables satisfy the given range.";
   }

}
