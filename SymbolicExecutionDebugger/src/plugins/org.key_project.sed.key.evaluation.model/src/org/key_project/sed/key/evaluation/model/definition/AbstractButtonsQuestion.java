package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.CollectionUtil;

public abstract class AbstractButtonsQuestion extends AbstractChoicesQuestion {
   private final boolean vertical;

   public AbstractButtonsQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, vertical, defaultChoice, validator, askForTrust, CollectionUtil.toList(choices));
   }

   public AbstractButtonsQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      super(name, label, defaultChoice, validator, askForTrust, choices);
      this.vertical = vertical;
   }

   public boolean isVertical() {
      return vertical;
   }
}
