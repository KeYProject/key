package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

public class RadioButtonsQuestion extends AbstractQuestion {
   private final String label;
   
   private final List<Choice> choices;
   
   private final boolean vertical;

   public RadioButtonsQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, Choice... choices) {
      this(name, label, vertical, defaultChoice, validator, CollectionUtil.toList(choices));
   }

   public RadioButtonsQuestion(String name, String label, boolean vertical, String defaultChoice, IValueValidator validator, List<Choice> choices) {
      super(name, defaultChoice, validator);
      this.vertical = vertical;
      this.label = label;
      this.choices = choices;
   }

   public boolean isVertical() {
      return vertical;
   }

   public String getLabel() {
      return label;
   }

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
