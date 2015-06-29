package org.key_project.sed.key.evaluation.model.input;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.CheckboxQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.definition.TextQuestion;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.util.LinkedHashMap;

public class QuestionInput extends Bean {
   public static final String PROP_VALUE = "value";

   public static final String PROP_VALUE_SET_AT = "valueSetAt";
   
   public static final String PROP_TRUST = "trust";

   public static final String PROP_TRUST_SET_AT = "trustSetAt";
   
   private final AbstractPageInput<?> pageInput;
   
   private final AbstractQuestion question;
   
   private final Map<Choice, List<QuestionInput>> choiceInputs;
   
   private final List<QuestionInput> childInputs;
   
   private String value;
   
   private long valueSetAt;
   
   /**
    * {@code Boolean#TRUE} if the user believes the value is right,
    * {@code Boolean#FALSE} if the user believes the value is wrong,
    * {@code null} if not yet defined. 
    */
   private Boolean trust;
   
   private long trustSetAt;

   public QuestionInput(AbstractPageInput<?> pageInput, AbstractQuestion question) {
      this.pageInput = pageInput;
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
                     childInputs.add(new QuestionInput(pageInput, childQuestion));
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
      if (question instanceof SectionQuestion) {
         SectionQuestion sectionQuestion = (SectionQuestion) question;
         childInputs = new ArrayList<QuestionInput>(sectionQuestion.countChildQuestions());
         for (AbstractQuestion childQuestion : sectionQuestion.getChildQuestions()) {
            childInputs.add(new QuestionInput(pageInput, childQuestion));
         }
      }
      else {
         childInputs = null;
      }
   }

   public QuestionInput[] getChildInputs() {
      return childInputs != null ?
             childInputs.toArray(new QuestionInput[childInputs.size()]) :
             new QuestionInput[0];
   }
   
   public int countChildInputs() {
      return childInputs != null ? childInputs.size() : 0;
   }

   public QuestionInput getChildInput(final String questionName) {
      if (childInputs != null) {
         return CollectionUtil.search(childInputs, new IFilter<QuestionInput>() {
            @Override
            public boolean select(QuestionInput element) {
               return ObjectUtil.equals(questionName, element.getQuestion().getName());
            }
         });
      }
      else {
         return null;
      }
   }

   public AbstractPageInput<?> getPageInput() {
      return pageInput;
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
   
   public long getValueSetAt() {
      return valueSetAt;
   }

   public void setValueSetAt(long valueSetAt) {
      long oldValue = getValueSetAt();
      this.valueSetAt = valueSetAt;
      firePropertyChange(PROP_VALUE_SET_AT, oldValue, getValueSetAt());
   }

   public Boolean getTrust() {
      return trust;
   }

   public void setTrust(Boolean trust) {
      Boolean oldValue = getTrust();
      this.trust = trust;
      firePropertyChange(PROP_TRUST, oldValue, getTrust());
   }

   public long getTrustSetAt() {
      return trustSetAt;
   }

   public void setTrustSetAt(long trustSetAt) {
      long oldValue = getTrustSetAt();
      this.trustSetAt = trustSetAt;
      firePropertyChange(PROP_TRUST_SET_AT, oldValue, getTrustSetAt());
   }

   public String validate() {
      // Validate input
      String errorMessage = validateValue();
      if (errorMessage == null && question.isAskForTrust()) {
         errorMessage = validateTrust();
      }
      // Validate choice inputs
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
      // Validate child inputs
      if (errorMessage == null && childInputs != null) {
         Iterator<QuestionInput> iter = childInputs.iterator();
         while (errorMessage == null && iter.hasNext()) {
            errorMessage = iter.next().validate();
         }
      }
      return errorMessage;
   }
   
   public String validateValue() {
      return question.validate(getValue());
   }
   
   public String validateTrust() {
      if (getTrust() == null) {
         return "Emoticon defining trust into answer of question '" + question.getLabel() + "' not selected.";
      }
      else {
         return null;
      }
   }
   
   public boolean isChoiceSelected(Choice choice) {
      if (value != null && choice != null) {
         String[] values = value.split(CheckboxQuestion.VALUE_SEPARATOR);
         return ArrayUtil.contains(values, choice.getValue());
      }
      else {
         return false;
      }
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

   public void reset() {
      setValue(question.getDefaultValue());
      setValueSetAt(0);
      setTrust(null);
      setTrustSetAt(0);
      if (choiceInputs != null) {
         for (List<QuestionInput> choiceInputList : choiceInputs.values()) {
            for (QuestionInput choiceInput : choiceInputList) {
               choiceInput.reset();
            }
         }
      }
      if (childInputs != null) {
         for (QuestionInput childInput : childInputs) {
            childInput.reset();
         }
      }
   }
   
   public Boolean checkCorrectness() {
      if (question.isEditable()) {
         if (question instanceof TextQuestion) {
            return null; // Correctness not supported
         }
         else if (question instanceof AbstractChoicesQuestion) {
            AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
            Set<Choice> remainingCorrectChoices = new HashSet<Choice>();
            for (Choice choice : choiceQuestion.getChoices()) {
               if (choice.isExpectedChecked()) {
                  remainingCorrectChoices.add(choice);
               }
            }
            if (!remainingCorrectChoices.isEmpty()) {
               Choice[] selectedChoices = getSelectedChoices();
               boolean correct = true;
               int i = 0;
               while (correct && i < selectedChoices.length) {
                  if (!remainingCorrectChoices.remove(selectedChoices[i])) {
                     correct = false;
                  }
                  i++;
               }
               return correct && remainingCorrectChoices.isEmpty();
            }
            else {
               return null; // Correctness not supported
            }
         }
         else {
            throw new IllegalStateException("Unsupported question: " + question);
         }
      }
      else {
         return null;
      }
   }
   
   public Boolean checkTrust() {
      if (trust != null) {
         Boolean correct = checkCorrectness();
         if (correct != null) {
            return correct.equals(getTrust());
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
}
