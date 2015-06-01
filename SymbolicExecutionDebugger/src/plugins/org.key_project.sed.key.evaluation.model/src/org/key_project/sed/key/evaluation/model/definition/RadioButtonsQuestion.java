package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public class RadioButtonsQuestion extends AbstractButtonsQuestion {
   public RadioButtonsQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, Choice... choices) {
      super(name, label, vertical, defaultChoice, validator, choices);
   }

   public RadioButtonsQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, List<Choice> choices) {
      super(name, label, vertical, defaultChoice, validator, choices);
   }

   @Override
   public boolean isMultiValued() {
      return false;
   }
}
