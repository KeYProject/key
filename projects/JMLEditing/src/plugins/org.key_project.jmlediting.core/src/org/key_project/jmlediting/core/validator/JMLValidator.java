package org.key_project.jmlediting.core.validator;

import org.key_project.jmlediting.core.dom.IASTNode;

public interface JMLValidator {
   /**
    * Method for checking if a given JML Spec (Represented by a node) is valid.
    *
    * @return
    */
   boolean isValid(IASTNode node);
}
