package org.key_project.sed.key.evaluation.model.definition;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public class TextQuestion extends AbstractQuestion {
   public TextQuestion(String name, String label, String defaultValue, IValueValidator validator, boolean askForTrust) {
      super(name, label, defaultValue, validator, askForTrust);
   }
}
