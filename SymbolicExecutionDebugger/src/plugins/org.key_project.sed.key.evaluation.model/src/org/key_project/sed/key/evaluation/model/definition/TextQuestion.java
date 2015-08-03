package org.key_project.sed.key.evaluation.model.definition;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public class TextQuestion extends AbstractQuestion {
   public TextQuestion(String name, String label, String defaultValue, IValueValidator validator, boolean askForTrust) {
      super(name, label, null, defaultValue, validator, askForTrust);
   }

   public TextQuestion(String name, String label, String description, String defaultValue, IValueValidator validator, boolean askForTrust) {
      super(name, label, description, defaultValue, validator, askForTrust);
   }

   public TextQuestion(String name, String label, String description, String defaultValue, IValueValidator validator, boolean askForTrust, Tool[] relatedTools) {
      super(name, label, description, defaultValue, validator, askForTrust, relatedTools);
   }
}
