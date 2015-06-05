package org.key_project.sed.key.evaluation.model.definition;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public abstract class AbstractQuestion {
   private final String name;
   
   private final String label;
   
   private final String defaultValue;
   
   private final IValueValidator validator;
   
   private final boolean askForTrust;

   public AbstractQuestion(String name) {
      this(name, null, null, null, false);
   }

   public AbstractQuestion(String name, String label, String defaultValue, IValueValidator validator, boolean askForTrust) {
      this.name = name;
      this.label = label;
      this.defaultValue = defaultValue;
      this.validator = validator;
      this.askForTrust = askForTrust;
   }

   public String getName() {
      return name;
   }

   public String getLabel() {
      return label;
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
   
   public boolean isAskForTrust() {
      return askForTrust;
   }

   public boolean isEditable() {
      return true;
   }

   @Override
   public String toString() {
      return name + " (" + getClass().getName() + ")";
   }
}
