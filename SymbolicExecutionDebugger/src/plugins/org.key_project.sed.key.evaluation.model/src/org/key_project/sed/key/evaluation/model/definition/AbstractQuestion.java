package org.key_project.sed.key.evaluation.model.definition;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.ArrayUtil;

public abstract class AbstractQuestion {
   private final String name;
   
   private final String label;
   
   private final String latexLabel;
   
   private final String description;
   
   private final String defaultValue;
   
   private final IValueValidator validator;
   
   private final boolean askForTrust;
   
   private final Tool[] relatedTools;
   
   private final boolean enabled;

   public AbstractQuestion(String name) {
      this(name, null, null, null, null, false, null);
   }

   public AbstractQuestion(String name, String label, String description, String defaultValue, IValueValidator validator, boolean askForTrust) {
      this(name, label, description, defaultValue, validator, askForTrust, null);
   }

   public AbstractQuestion(String name, String label, String description, String defaultValue, IValueValidator validator, boolean askForTrust, Tool[] relatedTools) {
      this(name, label, description, defaultValue, validator, askForTrust, relatedTools, true);
   }

   public AbstractQuestion(String name, String label, String description, String defaultValue, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled) {
      this(name, label, label, description, defaultValue, validator, askForTrust, relatedTools, enabled);
   }

   public AbstractQuestion(String name, String label, String latexLabel, String description, String defaultValue, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled) {
      this.name = name;
      this.label = label;
      this.latexLabel = latexLabel;
      this.description = description;
      this.defaultValue = defaultValue;
      this.validator = validator;
      this.askForTrust = askForTrust;
      this.relatedTools = relatedTools;
      this.enabled = enabled;
   }

   public String getName() {
      return name;
   }

   public String getLabel() {
      return label;
   }

   public String getLatexLabel() {
      return latexLabel;
   }

   public String getDescription() {
      return description;
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
   
   public boolean isToolRelated() {
      return !ArrayUtil.isEmpty(relatedTools);
   }
   
   public Tool[] getRelatedTools() {
      return relatedTools;
   }

   public boolean isAskForTrust() {
      return askForTrust;
   }

   public boolean isEditable() {
      return true;
   }

   public boolean isEnabled() {
      return enabled;
   }

   @Override
   public String toString() {
      return name + " (" + getClass().getName() + ")";
   }
}
