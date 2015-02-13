package org.key_project.jmlediting.core.validation;

import org.key_project.jmlediting.core.dom.IASTNode;

public abstract class JMLPositionValidator implements IJMLValidator {

   private int offset;

   /*
    * (non-Javadoc)
    * 
    * @see
    * org.key_project.jmlediting.core.validator.JMLValidator#isValid(org.key_project
    * .jmlediting.core.dom.IASTNode)
    */
   @Override
   public boolean validate(final IJMLValidationContext context, IASTNode node) {
      return this.validateForPosition(context, null);
   }

   protected abstract boolean validateForPosition(
         final IJMLValidationContext context, IASTNode node);

}
