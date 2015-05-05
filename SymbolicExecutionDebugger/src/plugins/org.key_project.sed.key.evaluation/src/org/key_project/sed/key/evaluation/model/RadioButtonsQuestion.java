package org.key_project.sed.key.evaluation.model;

import java.util.List;

import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.util.java.CollectionUtil;

public class RadioButtonsQuestion extends AbstractQuestion {
   private final String label;
   
   private final List<Choice> choices;

   public RadioButtonsQuestion(String name, String label, String defaultChoice, IValueValidator validator, Choice... choices) {
      this(name, label, defaultChoice, validator, CollectionUtil.toList(choices));
   }

   public RadioButtonsQuestion(String name, String label, String defaultChoice, IValueValidator validator, List<Choice> choices) {
      super(name, defaultChoice, validator);
      this.label = label;
      this.choices = choices;
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
   
   public static class Choice {
      private final String text;
      
      private final String value;
      
      private final String tooltip;

      public Choice(String text, String value) {
         this(text, value, null);
      }

      public Choice(String text, String value, String tooltip) {
         this.text = text;
         this.value = value;
         this.tooltip = tooltip;
      }

      public String getText() {
         return text;
      }

      public String getValue() {
         return value;
      }

      public String getTooltip() {
         return tooltip;
      }
   }
}
