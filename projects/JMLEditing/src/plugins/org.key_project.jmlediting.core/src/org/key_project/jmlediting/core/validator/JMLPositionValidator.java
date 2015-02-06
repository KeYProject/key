package org.key_project.jmlediting.core.validator;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.Position;

public abstract class JMLPositionValidator implements JMLValidator {

   private Position p;

   /*
    * (non-Javadoc)
    * 
    * @see
    * org.key_project.jmlediting.core.validator.JMLValidator#isValid(org.key_project
    * .jmlediting.core.dom.IASTNode)
    */
   @Override
   public boolean isValid(final IASTNode node) {
      return this.isValidForPosition(node, this.p);
   }

   abstract boolean isValidForPosition(final IASTNode node, final Position p);

}
