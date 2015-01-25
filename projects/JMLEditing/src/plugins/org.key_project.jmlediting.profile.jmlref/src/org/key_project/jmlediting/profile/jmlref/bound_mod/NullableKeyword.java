package org.key_project.jmlediting.profile.jmlref.bound_mod;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

/**
 * The implementation of the nullable keyword.
 *
 * @author Moritz Lichter
 *
 */
public class NullableKeyword extends AbstractEmptyKeyword implements
      IBoundVarModifierKeyword {

   /**
    * Creates a new instance.
    */
   public NullableKeyword() {
      super("nullable");
   }

   @Override
   public String getDescription() {
      return "Specifies that a bound logical variable is allowed to be null.\n"
            + "In order to quantify over the elements of a type named non_null or "
            + "nullable is necessary to provide an explicit nullity modifier.";
   }

}
