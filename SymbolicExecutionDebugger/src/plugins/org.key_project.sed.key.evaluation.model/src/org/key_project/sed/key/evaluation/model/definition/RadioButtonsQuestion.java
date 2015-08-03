package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.eclipse.swt.graphics.Image;
import org.key_project.sed.key.evaluation.model.validation.IValueValidator;

public class RadioButtonsQuestion extends AbstractButtonsQuestion {
   public RadioButtonsQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, null, null, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public RadioButtonsQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, null, null, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public RadioButtonsQuestion(String name, String label, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, null, image, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public RadioButtonsQuestion(String name, String label, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, null, image, vertical, defaultChoice, validator, askForTrust, choices);
   }
   
   public RadioButtonsQuestion(String name, String label, String description, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, description, null, vertical, defaultChoice, validator, askForTrust, choices);
   }
   
   public RadioButtonsQuestion(String name, String label, String description, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, Choice... choices) {
      this(name, label, description, null, vertical, defaultChoice, validator, askForTrust, relatedTools, choices);
   }

   public RadioButtonsQuestion(String name, String label, String description, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, description, null, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public RadioButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      super(name, label, description, image, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public RadioButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, Choice... choices) {
      super(name, label, description, image, vertical, defaultChoice, validator, askForTrust, relatedTools, choices);
   }

   public RadioButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      super(name, label, description, image, vertical, defaultChoice, validator, askForTrust, choices);
   }

   public RadioButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, List<Choice> choices) {
      super(name, label, description, image, vertical, defaultChoice, validator, askForTrust, relatedTools, choices);
   }

   @Override
   public boolean isMultiValued() {
      return false;
   }
}
