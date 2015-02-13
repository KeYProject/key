package org.key_project.jmlediting.core.validation;

import org.key_project.jmlediting.core.dom.IASTNode;

public interface IJMLValidator {
   /**
    * Method for checking if a given JMLComments Specifications (Represented by
    * a node) are valid.
    *
    * @param context
    *           TODO
    * @param node
    *           TODO
    *
    * @return
    */
   boolean validate(IJMLValidationContext context, IASTNode node);
}
