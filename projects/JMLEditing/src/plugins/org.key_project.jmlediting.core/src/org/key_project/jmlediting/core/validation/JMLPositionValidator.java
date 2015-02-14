package org.key_project.jmlediting.core.validation;

import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * Class for Validating JML.
 *
 * @author David Giessing
 *
 */
public abstract class JMLPositionValidator implements IJMLValidator {

   /*
    * (non-Javadoc)
    *
    * @see
    * org.key_project.jmlediting.core.validator.JMLValidator#isValid(org.key_project
    * .jmlediting.core.dom.IASTNode)
    */
   @Override
   public abstract List<IMarker> validate(final IJMLValidationContext context,
         final IASTNode node);

   /**
    * Method for checking if a given JML Specification represented by node is
    * valid.
    *
    * @param context
    *           the Validation Context
    * @param node
    *           the Specification to validate
    * @return an IMarker if the Specification is invalid, null if it is valid
    */
   protected abstract IMarker validateNode(final IJMLValidationContext context,
         IASTNode node);

}
