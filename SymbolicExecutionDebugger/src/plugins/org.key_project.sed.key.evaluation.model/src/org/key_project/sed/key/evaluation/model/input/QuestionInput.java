package org.key_project.sed.key.evaluation.model.input;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public class QuestionInput extends Bean {
   public static final String PROP_VALUE = "value";
   
   private final AbstractQuestion question;
   
   private final Map<Choice, List<QuestionInput>> choiceInputs;
   
   private String value;

   public QuestionInput(AbstractQuestion question) {
      this.question = question;
      this.value = question.getDefaultValue();
      if (question instanceof RadioButtonsQuestion) {
         RadioButtonsQuestion rq = (RadioButtonsQuestion) question;
         if (rq.hasChildQuestions()) {
            choiceInputs = new HashMap<Choice, List<QuestionInput>>();
            for (Choice choice : rq.getChoices()) {
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
               return ObjectUtil.equals(element.getText(), choiceText);
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
   
   public String validate() {
      // Validate input
      String errorMessage = question.validate(getValue());
      // Validate child inputs
      if (errorMessage == null && hasChoiceInputs()) {
         Choice selectedChoice = getSelectedChoice();
         if (selectedChoice != null) {
            List<QuestionInput> childInputs = choiceInputs.get(selectedChoice);
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

   public Choice getSelectedChoice() {
      return CollectionUtil.search(choiceInputs.keySet(), new IFilter<Choice>() {
         @Override
         public boolean select(Choice element) {
            return ObjectUtil.equals(value, element.getText());
         }
      });
   }
}
