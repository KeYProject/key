package org.key_project.sed.key.evaluation.model.definition;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public abstract class AbstractChoicesQuestion extends AbstractQuestion {
   public static final String VALUE_SEPARATOR = ",";
   
   private final List<Choice> choices;
   
   private final Set<String> notCorrectnessRelevantChoiceValues;

   public AbstractChoicesQuestion(String name, String label, String description, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, description, defaultChoice, validator, askForTrust, null, CollectionUtil.toList(choices));
   }

   public AbstractChoicesQuestion(String name, String label, String description, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, Choice... choices) {
      this(name, label, description, defaultChoice, validator, askForTrust, relatedTools, CollectionUtil.toList(choices));
   }

   public AbstractChoicesQuestion(String name, String label, String description, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      this(name, label, description, defaultChoice, validator, askForTrust, null, choices);
   }

   public AbstractChoicesQuestion(String name, String label, String description, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, List<Choice> choices) {
      this(name, label, description, defaultChoice, validator, askForTrust, relatedTools, true, choices);
   }

   public AbstractChoicesQuestion(String name, String label, String description, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled, List<Choice> choices) {
      this(name, label, description, defaultChoice, validator, askForTrust, relatedTools, enabled, choices, null);
   }

   public AbstractChoicesQuestion(String name, String label, String description, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled, List<Choice> choices, Set<String> notCorrectnessRelevantChoiceValues) {
      this(name, label, label, description, defaultChoice, validator, askForTrust, relatedTools, enabled, choices, notCorrectnessRelevantChoiceValues);
   }

   public AbstractChoicesQuestion(String name, String label, String latexLabel, String description, String defaultChoice, IValueValidator validator, boolean askForTrust, Tool[] relatedTools, boolean enabled, List<Choice> choices, Set<String> notCorrectnessRelevantChoiceValues) {
      super(name, label, latexLabel, description, defaultChoice, validator, askForTrust, relatedTools, enabled);
      this.choices = choices;
      this.notCorrectnessRelevantChoiceValues = notCorrectnessRelevantChoiceValues;
      validateChocies(choices);
   }
   
   protected void validateChocies(List<Choice> choices) {
      // Ensure that all choices have different values and names
      Set<String> usedTexts = new HashSet<String>();
      Set<String> usedValues = new HashSet<String>();
      for (Choice choice : choices) {
         if (!usedTexts.add(choice.getText())) {
            throw new IllegalStateException("Choice text '" + choice.getText() + "' used multiple times.");
         }
         if (!usedValues.add(choice.getValue())) {
            throw new IllegalStateException("Choice value '" + choice.getValue() + "' used multiple times.");
         }
      }
      // Ensure that multi values does not use the separator
      if (isMultiValued()) {
         for (Choice choice : choices) {
            if (choice.getValue().contains(VALUE_SEPARATOR)) {
               throw new IllegalStateException("Choice value '" + choice.getValue() + "' contains '" + VALUE_SEPARATOR + "'.");
            }
         }
      }
   }
   
   public Set<Choice> getCorrectChoices() {
      Set<Choice> correctChoices = new LinkedHashSet<Choice>();
      for (Choice choice : choices) {
         if (choice.isExpectedChecked()) {
            correctChoices.add(choice);
         }
      }
      return correctChoices;
   }
   
   public abstract boolean isMultiValued();

   public Choice[] getChoices() {
      return choices.toArray(new Choice[choices.size()]);
   }
   
   public Choice getChoice(final String value) {
      return CollectionUtil.search(choices, new IFilter<Choice>() {
         @Override
         public boolean select(Choice element) {
            return ObjectUtil.equals(value, element.getValue());
         }
      });
   }

   public int countChoices() {
      return choices.size();
   }
   
   public boolean hasChildQuestions() {
      return CollectionUtil.search(choices, new IFilter<Choice>() {
         @Override
         public boolean select(Choice element) {
            return element.countChildQuestions() >= 1;
         }
      }) != null;
   }
   
   public boolean isChoiceCorrectnessRelevant(Choice choice) {
      if (!CollectionUtil.isEmpty(notCorrectnessRelevantChoiceValues)) {
         return !notCorrectnessRelevantChoiceValues.contains(choice.getValue());
      }
      else {
         return true;
      }
   }
}
