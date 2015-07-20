package org.key_project.sed.key.evaluation.model.definition;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

public abstract class AbstractChoicesQuestion extends AbstractQuestion {
   public static final String VALUE_SEPARATOR = ",";
   
   private final List<Choice> choices;

   public AbstractChoicesQuestion(String name, String label, String defaultChoice, IValueValidator validator, boolean askForTrust, Choice... choices) {
      this(name, label, defaultChoice, validator, askForTrust, CollectionUtil.toList(choices));
   }

   public AbstractChoicesQuestion(String name, String label, String defaultChoice, IValueValidator validator, boolean askForTrust, List<Choice> choices) {
      super(name, label, defaultChoice, validator, askForTrust);
      this.choices = choices;
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
}
