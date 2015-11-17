package org.key_project.sed.key.evaluation.model.validation;

import org.key_project.util.java.ObjectUtil;

public class FixedValueValidator implements IValueValidator {
   private final String expectedValue;
   
   private final String errorMessage;

   public FixedValueValidator(String expectedValue, String errorMessage) {
      this.expectedValue = expectedValue;
      this.errorMessage = errorMessage;
   }

   @Override
   public String validate(String value) {
      if (!ObjectUtil.equals(expectedValue, value)) {
         return errorMessage;
      }
      else {
         return null;
      }
   }
}
