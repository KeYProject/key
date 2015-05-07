package org.key_project.sed.key.evaluation.model.definition;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public abstract class AbstractQuestion {
   private final String name;
   
   private final String defaultValue;
   
   private final IValueValidator validator;

   public AbstractQuestion(String name) {
      this(name, null, null);
   }

   public AbstractQuestion(String name, String defaultValue, IValueValidator validator) {
      this.name = name;
      this.defaultValue = defaultValue;
      this.validator = validator;
   }

   public String getName() {
      return name;
   }

   public String getDefaultValue() {
      return defaultValue;
   }
   
   public String validate(String value) {
      if (validator != null) {
         return validator.validate(value);
      }
      else {
         return null;
      }
   }
   
   public boolean isEditable() {
      return true;
   }
}
