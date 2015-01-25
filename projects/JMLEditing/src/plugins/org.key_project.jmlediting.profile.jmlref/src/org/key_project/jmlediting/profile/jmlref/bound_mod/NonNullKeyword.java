package org.key_project.jmlediting.profile.jmlref.bound_mod;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

/**
 * Implementation of the non_null keyword, which is not reserved.
 *
 * @author Moritz Lichter
 *
 */
public class NonNullKeyword extends AbstractEmptyKeyword implements
      IBoundVarModifierKeyword {

   /**
    * Creates a new instance.
    */
   public NonNullKeyword() {
      super("non_null");
   }

   @Override
   public String getDescription() {
      return "Specifies that a bound logical variable is not allowed to be null.\n"
            + "In order to quantify over the elements of a type named non_null or "
            + "nullable is necessary to provide an explicit nullity modifier.";
   }

}
