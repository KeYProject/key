package org.key_project.sed.key.evaluation.model.validation;

import org.key_project.util.java.StringUtil;

public class NotUndefinedValueValidator implements IValueValidator {
   private final String errorMessage;

   public NotUndefinedValueValidator(String errorMessage) {
      this.errorMessage = errorMessage;
   }

   @Override
   public String validate(String value) {
      if (StringUtil.isTrimmedEmpty(value)) {
         return errorMessage;
      }
      else {
         return null;
      }
   }
}
