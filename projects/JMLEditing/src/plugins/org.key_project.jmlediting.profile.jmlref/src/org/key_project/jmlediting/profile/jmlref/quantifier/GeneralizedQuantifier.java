package org.key_project.jmlediting.profile.jmlref.quantifier;

public class GeneralizedQuantifier extends AbstractQuantifierKeyword {

   public GeneralizedQuantifier(final String keyword) {
      super(keyword);
   }

   @Override
   public String getDescription() {
      return "The quantifiers \\max, \\min, \\product, and \\sum, are generalized quantifiers "
            + "that return the maximum, minimum, product, or sum of the values of the "
            + "expressions given, where the variables satisfy the given range. The expression "
            + "in the body must be of a built-in numeric type, such as int or double; the type "
            + "of the quantified expression as a whole is the type of its body.";
   }

}
