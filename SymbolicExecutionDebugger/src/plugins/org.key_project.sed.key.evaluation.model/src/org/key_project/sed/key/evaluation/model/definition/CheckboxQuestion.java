package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.eclipse.swt.graphics.Image;
import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public class CheckboxQuestion extends AbstractButtonsQuestion {
   public CheckboxQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, null, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, null, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      super(name, label, image, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      super(name, label, image, vertical, defaultChoice, validator, askForTrust, choices);
   }

   @Override
   public boolean isMultiValued() {
      return true;
   }
}
