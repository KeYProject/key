package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public class CheckboxQuestion extends AbstractButtonsQuestion {
   public CheckboxQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, Choice... choices) {
      super(name, label, vertical, defaultChoice, validator, choices);
   }

   public CheckboxQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, List<Choice> choices) {
      super(name, label, vertical, defaultChoice, validator, choices);
   }

   @Override
   public boolean isMultiValued() {
      return true;
   }
}
