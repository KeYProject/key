package org.key_project.sed.key.evaluation.model.input;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.CheckboxQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.IQuestionWithCildren;
import org.key_project.sed.key.evaluation.model.definition.TextQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
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
    * The users {@link Trust} into the correctness of the answer or {@code null} if not yet defined.
    */
   private Trust trust;
   
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
      if (question instanceof IQuestionWithCildren) {
         IQuestionWithCildren withChildrenQuestion = (IQuestionWithCildren) question;
         childInputs = new ArrayList<QuestionInput>(withChildrenQuestion.countChildQuestions());
         for (AbstractQuestion childQuestion : withChildrenQuestion.getChildQuestions()) {
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

   public Trust getTrust() {
      return trust;
   }

   public void setTrust(Trust trust) {
      Trust oldValue = getTrust();
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

   public String validate(Tool currentTool) {
      if (question.isEnabled() &&
          (!question.isToolRelated() ||
           ArrayUtil.contains(question.getRelatedTools(), currentTool))) {
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
                     errorMessage = iter.next().validate(currentTool);
                  }
               }
            }
         }
         // Validate child inputs
         if (errorMessage == null && childInputs != null) {
            Iterator<QuestionInput> iter = childInputs.iterator();
            while (errorMessage == null && iter.hasNext()) {
               errorMessage = iter.next().validate(currentTool);
            }
         }
         return errorMessage;
      }
      else {
         return null;
      }
   }
   
   public String validateValue() {
      return question.validate(getValue());
   }
   
   public String validateTrust() {
      if (getTrust() == null) {
         return "Emoticon defining trust in answer of question '" + question.getLabel() + "' not selected.";
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
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.isMultiValued()) {
            if (!StringUtil.isEmpty(value)) {
               final String[] values = value.split(AbstractChoicesQuestion.VALUE_SEPARATOR);
               final Set<String> valuesSet = CollectionUtil.toSet(values);
               List<Choice> choices = CollectionUtil.searchAll(CollectionUtil.toList(choiceQuestion.getChoices()), new IFilter<Choice>() {
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
            Choice choice = ArrayUtil.search(choiceQuestion.getChoices(), new IFilter<Choice>() {
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
            Set<Choice> remainingCorrectChoices = choiceQuestion.getCorrectChoices();
            if (!remainingCorrectChoices.isEmpty()) {
               Choice[] selectedChoices = getSelectedChoices();
               boolean correct = true;
               int i = 0;
               while (correct && i < selectedChoices.length) {
                  if (choiceQuestion.isChoiceCorrectnessRelevant(selectedChoices[i])) { // Skip for instance the gave up choice in the understanding proof attempts evaluation.
                     if (!remainingCorrectChoices.remove(selectedChoices[i])) {
                        correct = false;
                     }
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
   
   public BigDecimal computeCorrectnessScore() {
      Integer difference = computeCorrectWrongDifference();
      if (difference != null) {
         if (difference.intValue() > 0) {
            Integer correctCount = countCorrectAnswers();
            return new BigDecimal(difference).divide(new BigDecimal(correctCount), 2, RoundingMode.HALF_EVEN);
         }
         else {
            Integer wrongCount = countWrongAnswers();
            return new BigDecimal(difference).divide(new BigDecimal(wrongCount), 2, RoundingMode.HALF_EVEN);
         }
      }
      else {
         return null;
      }
   }
   
   public Integer computeCorrectWrongDifference() {
      if (question.isEditable()) {
         if (question instanceof TextQuestion) {
            return null; // Correctness not supported
         }
         else if (question instanceof AbstractChoicesQuestion) {
            AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
            Set<Choice> correctChoices = choiceQuestion.getCorrectChoices();
            if (!correctChoices.isEmpty()) {
               Choice[] selectedChoices = getSelectedChoices();
               int correctCount = 0;
               for (Choice choice : selectedChoices) {
                  if (choiceQuestion.isChoiceCorrectnessRelevant(choice)) { // Skip for instance the gave up choice in the understanding proof attempts evaluation.
                     if (correctChoices.contains(choice)) {
                        correctCount++;
                     }
                     else {
                        correctCount--;
                     }
                  }
               }
               return correctCount;
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
   
   /**
    * Returns the number of correct answers.
    * @return The number of correct answers or {@code null} if not available.
    */
   public Integer countCorrectAnswers() {
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         Set<Choice> correctChoices = choiceQuestion.getCorrectChoices();
         if (!CollectionUtil.isEmpty(correctChoices)) {
            return correctChoices.size();
         }
         else {
            return 0;
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the number of wrong answers.
    * @return The number of wrong answers or {@code null} if not available.
    */
   public Integer countWrongAnswers() {
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         Set<Choice> correctChoices = choiceQuestion.getCorrectChoices();
         int wrongCount = 0;
         for (Choice choice : choiceQuestion.getChoices()) {
            if (choiceQuestion.isChoiceCorrectnessRelevant(choice)) { // Skip for instance the gave up choice in the understanding proof attempts evaluation.
               if (!correctChoices.contains(choice)) {
                  wrongCount++;
               }
            }
         }
         return wrongCount;
      }
      else {
         return null;
      }
   }
   
   /**
    * Computes the achieved trust score as follows:
    * <table border="1">
    *    <tr><td>&nbsp;</td><td>Correct</td><td>Wrong</td></tr>
    *    <tr><td>{@link Trust#SURE}</td><td>2</td><td>-2</td></tr>
    *    <tr><td>{@link Trust#EDUCATED_GUESS}</td><td>1</td><td>-1</td></tr>
    *    <tr><td>{@link Trust#UNSURE}</td><td>-1</td><td>1</td></tr>
    * </table>
    * @return The computed trust score or {@code null} if no result is available.
    */
   public Integer computeTrustScore() {
      if (trust != null) {
         Boolean correct = checkCorrectness();
         return doTrustScoreComputation(correct);
      }
      else {
         return null;
      }
   }
   
   /**
    * Utility method of {@link #computeTrustScore()}.
    * @param correct The achieved correctness.
    * @return The computed trust score or {@code null} if not available.
    */
   private Integer doTrustScoreComputation(Boolean correct) {
      if (correct != null) {
         if (Trust.SURE.equals(trust)) {
            return correct.booleanValue() ? 2 : -2;
         }
         else if (Trust.EDUCATED_GUESS.equals(trust)) {
            return correct.booleanValue() ? 1 : -1;
         }
         else if (Trust.UNSURE.equals(trust)) {
            return correct.booleanValue() ? -1 : 1;
         }
         else {
            throw new IllegalStateException("Unsupported trust: " + trust);
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Computes the achieved partial trust score which is
    * {@link #computeCorrectnessScore()} * trust score.
    * @return The computed trust score or {@code null} if no result is available.
    */
   public BigDecimal computePartialTrustScore() {
      if (trust != null) {
         Integer correctnessScore = computeCorrectWrongDifference();
         Boolean correct = correctnessScore != null ? correctnessScore.intValue() > 0 : null;
         Integer trustScore = doTrustScoreComputation(correct);
         return trustScore != null ? computeCorrectnessScore().multiply(new BigDecimal(trustScore)) : null;
      }
      else {
         return null;
      }
   }
}
