package org.key_project.jmlediting.core.validation;

import org.key_project.jmlediting.core.dom.IASTNode;

public interface IJMLValidator {
   /**
    * Method for checking if a given JML Spec (Represented by a node) is valid.
    *
    * @param context
    *           TODO
    * @param node TODO
    *
    * @return
    */
   boolean validate(IJMLValidationContext context, IASTNode node);
}
