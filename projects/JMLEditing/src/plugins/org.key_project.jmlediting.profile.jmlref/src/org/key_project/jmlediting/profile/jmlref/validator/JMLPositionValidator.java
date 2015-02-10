package org.key_project.jmlediting.profile.jmlref.validator;

import org.key_project.jmlediting.core.utilities.Position;

public abstract class JMLPositionValidator implements IJMLValidator {

   private Position p;

   /*
    * (non-Javadoc)
    *
    * @see
    * org.key_project.jmlediting.core.validator.JMLValidator#isValid(org.key_project
    * .jmlediting.core.dom.IASTNode)
    */
   @Override
   public boolean isValid(final IJMLValidationContext context) {
      return this.isValidForPosition(context, this.p);
   }

   abstract boolean isValidForPosition(final IJMLValidationContext context,
         final Position p);

}
