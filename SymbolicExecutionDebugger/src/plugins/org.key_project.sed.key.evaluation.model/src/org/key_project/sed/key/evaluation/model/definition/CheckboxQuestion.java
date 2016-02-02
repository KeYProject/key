package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;
import java.util.Set;

import org.eclipse.swt.graphics.Image;
import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.CollectionUtil;

public class CheckboxQuestion extends AbstractButtonsQuestion {
   public CheckboxQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, null, null, vertical, defaultChoice, validator, askForTrust, choices);
   }
   
   public CheckboxQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Set<String> notCorrectnessRelevantChoiceValues, Choice... choices) {
      this(name, label, null, null, vertical, defaultChoice, validator, askForTrust, notCorrectnessRelevantChoiceValues, choices);
   }
   
   public CheckboxQuestion(String name, String label, String latexLabel, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Set<String> notCorrectnessRelevantChoiceValues, Choice... choices) {
      this(name, label, latexLabel, null, null, vertical, defaultChoice, validator, askForTrust, notCorrectnessRelevantChoiceValues, choices);
   }

   public CheckboxQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, null, null, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, null, image, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, null, image, vertical, defaultChoice, validator, askForTrust, choices);
   }
   
   public CheckboxQuestion(String name, String label, String description, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, description, null, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, String description, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, description, null, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      super(name, label, description, image, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, String latexLabel, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      super(name, label, latexLabel, description, image, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public CheckboxQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Set<String> notCorrectnessRelevantChoiceValues, Choice... choices) {
      super(name, label, description, image, vertical, defaultChoice, validator, askForTrust, null, true, CollectionUtil.toList(choices), notCorrectnessRelevantChoiceValues);
   }

   public CheckboxQuestion(String name, String label, String latexLabel, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Set<String> notCorrectnessRelevantChoiceValues, Choice... choices) {
      super(name, label, latexLabel, description, image, vertical, defaultChoice, validator, askForTrust, null, true, CollectionUtil.toList(choices), notCorrectnessRelevantChoiceValues);
   }

   public CheckboxQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      super(name, label, description, image, vertical, defaultChoice, validator, askForTrust, choices);
   }
   
   public CheckboxQuestion(String name, String label, String description, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, boolean enabled, Choice... choices) {
      this(name, label, description, null, vertical, defaultChoice, validator, askForTrust, enabled, choices);
   }

   public CheckboxQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, boolean enabled, Choice... choices) {
      super(name, label, description, image, vertical, defaultChoice, validator, askForTrust, enabled, choices);
   }

   @Override
   public boolean isMultiValued() {
      return true;
   }
}
