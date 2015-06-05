package org.key_project.sed.key.evaluation.model.input;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.util.LinkedHashMap;

public class QuestionInput extends Bean {
   public static final String PROP_VALUE = "value";
   
   public static final String PROP_TRUST = "trust";
   
   private final AbstractQuestion question;
   
   private final Map<Choice, List<QuestionInput>> choiceInputs;
   
   private String value;
   
   /**
    * {@code Boolean#TRUE} if the user believes the value is right,
    * {@code Boolean#FALSE} if the user believes the value is wrong,
    * {@code null} if not yet defined. 
    */
   private Boolean trust;

   public QuestionInput(AbstractQuestion question) {
      this.question = question;
      this.value = question.getDefaultValue();
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.hasChildQuestions()) {
            choiceInputs = new LinkedHashMap<Choice, List<QuestionInput>>();
            for (Choice choice : choiceQuestion.getChoices()) {
               AbstractQuestion[] childQuestions = choice.getChildQuestions();
               if (!ArrayUtil.isEmpty(childQuestions)) {
                  List<QuestionInput> childInputs = new ArrayList<QuestionInput>(childQuestions.length);
                  for (AbstractQuestion childQuestion : childQuestions) {
                     childInputs.add(new QuestionInput(childQuestion));
                  }
                  choiceInputs.put(choice, childInputs); 
               }
            }
         }
         else {
            choiceInputs = null;
         }
      }
      else {
         choiceInputs = null;
      }
   }

   public AbstractQuestion getQuestion() {
      return question;
   }
   
   public boolean hasChoiceInputs() {
      return choiceInputs != null && !choiceInputs.isEmpty();
   }
   
   public Choice[] getChoices() {
      if (choiceInputs != null) {
         Set<Choice> keys = choiceInputs.keySet();
         return keys.toArray(new Choice[keys.size()]);
      }
      else {
         return new Choice[0];
      }
   }

   public Choice getChoice(final String choiceText) {
      if (choiceInputs != null) {
         return CollectionUtil.search(choiceInputs.keySet(), new IFilter<Choice>() {
            @Override
            public boolean select(Choice element) {
               return ObjectUtil.equals(element.getValue(), choiceText);
            }
         });
      }
      else {
         return null;
      }
   }
   
   public QuestionInput[] getChoiceInputs(Choice choice) {
      if (choiceInputs != null && choice != null) {
         List<QuestionInput> list = choiceInputs.get(choice);
         return list != null ? list.toArray(new QuestionInput[list.size()]) : null;
      }
      else {
         return null;
      }
   }

   public String getValue() {
      return value;
   }

   public void setValue(String value) {
      String oldValue = getValue();
      this.value = value;
      firePropertyChange(PROP_VALUE, oldValue, getValue());
   }
   
   public Boolean getTrust() {
      return trust;
   }

   public void setTrust(Boolean trust) {
      Boolean oldValue = getTrust();
      this.trust = trust;
      firePropertyChange(PROP_TRUST, oldValue, getTrust());
   }

   public String validate() {
      // Validate input
      String errorMessage = question.validate(getValue());
      if (errorMessage == null && question.isAskForTrust()) {
         if (getTrust() == null) {
            errorMessage = "Trust into answer of question '" + question.getLabel() + "' is not defined.";
         }
      }
      // Validate child inputs
      if (errorMessage == null && hasChoiceInputs()) {
         Choice[] selectedChoices = getSelectedChoices();
         for (int i = 0; errorMessage == null && i < selectedChoices.length; i++) {
            List<QuestionInput> childInputs = choiceInputs.get(selectedChoices[i]);
            if (childInputs != null) {
               Iterator<QuestionInput> iter = childInputs.iterator();
               while (errorMessage == null && iter.hasNext()) {
                  errorMessage = iter.next().validate();
               }
            }
         }
      }
      return errorMessage;
   }

   public Choice[] getSelectedChoices() {
      if (choiceInputs != null) {
         if (((AbstractChoicesQuestion) question).isMultiValued()) {
            if (!StringUtil.isEmpty(value)) {
               final String[] values = value.split(AbstractChoicesQuestion.VALUE_SEPARATOR);
               final Set<String> valuesSet = CollectionUtil.toSet(values);
               List<Choice> choices = CollectionUtil.searchAll(choiceInputs.keySet(), new IFilter<Choice>() {
                  @Override
                  public boolean select(Choice element) {
                     return valuesSet.contains(element.getValue());
                  }
               });
               return choices.toArray(new Choice[choices.size()]);
            }
            else {
               return new Choice[0];
            }
         }
         else {
            Choice choice = CollectionUtil.search(choiceInputs.keySet(), new IFilter<Choice>() {
               @Override
               public boolean select(Choice element) {
                  return ObjectUtil.equals(value, element.getValue());
               }
            });
            return choice != null ? new Choice[] {choice} : new Choice[0];
         }
      }
      else {
         return new Choice[0];
      }      
   }

   @Override
   public String toString() {
      return "Input of " + question;
   }
}
