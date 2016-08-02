package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;
import java.util.Set;

import org.eclipse.swt.graphics.Image;
import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.CollectionUtil;

public abstract class AbstractButtonsQuestion extends AbstractChoicesQuestion {
   private final boolean vertical;
   
   private final Image image;

   public AbstractButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, description, image, vertical, defaultChoice, validator, askForTrust, null, CollectionUtil.toList(choices));
   }

   public AbstractButtonsQuestion(String name, String label, String latexLabel, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, latexLabel, description, image, vertical, defaultChoice, validator, askForTrust, null, CollectionUtil.toList(choices));
   }

   public AbstractButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, boolean enabled, Choice... choices) {
      this(name, label, description, image, vertical, defaultChoice, validator, askForTrust, null, enabled, CollectionUtil.toList(choices));
   }

   public AbstractButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, Choice... choices) {
      this(name, label, description, image, vertical, defaultChoice, validator, askForTrust, relatedTools, CollectionUtil.toList(choices));
   }

   public AbstractButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, description, image, vertical, defaultChoice, validator, askForTrust, null, choices);
   }

   public AbstractButtonsQuestion(String name, String label, String latexLabel, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, latexLabel, description, image, vertical, defaultChoice, validator, askForTrust, null, choices);
   }

   public AbstractButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, List<Choice> choices) {
      this(name, label, description, image, vertical, defaultChoice, validator, askForTrust, relatedTools, true, choices);
   }

   public AbstractButtonsQuestion(String name, String label, String latexLabel, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, List<Choice> choices) {
      this(name, label, latexLabel, description, image, vertical, defaultChoice, validator, askForTrust, relatedTools, true, choices);
   }

   public AbstractButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled, List<Choice> choices) {
      this(name, label, description, image, vertical, defaultChoice, validator, askForTrust, relatedTools, enabled, choices, null);
   }

   public AbstractButtonsQuestion(String name, String label, String latexLabel, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled, List<Choice> choices) {
      this(name, label, latexLabel, description, image, vertical, defaultChoice, validator, askForTrust, relatedTools, enabled, choices, null);
   }

   public AbstractButtonsQuestion(String name, String label, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled, List<Choice> choices, Set<String> notCorrectnessRelevantChoiceValues) {
      this(name, label, label, description, image, vertical, defaultChoice, validator, askForTrust, relatedTools, enabled, choices, notCorrectnessRelevantChoiceValues);
   }

   public AbstractButtonsQuestion(String name, String label, String latexLabel, String description, Image image, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled, List<Choice> choices, Set<String> notCorrectnessRelevantChoiceValues) {
      super(name, label, latexLabel, description, defaultChoice, validator, askForTrust, relatedTools, enabled, choices, notCorrectnessRelevantChoiceValues);
      this.image = image;
      this.vertical = vertical;
   }

   public Image getImage() {
      return image;
   }

   public boolean isVertical() {
      return vertical;
   }
}
