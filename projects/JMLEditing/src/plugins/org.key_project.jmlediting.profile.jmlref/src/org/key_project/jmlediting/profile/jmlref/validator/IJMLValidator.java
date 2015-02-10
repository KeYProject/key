package org.key_project.jmlediting.profile.jmlref.validator;

public interface IJMLValidator {
   /**
    * Method for checking if a given JML Spec (Represented by a node) is valid.
    * 
    * @param context
    *           TODO
    *
    * @return
    */
   boolean isValid(IJMLValidationContext context);
}
