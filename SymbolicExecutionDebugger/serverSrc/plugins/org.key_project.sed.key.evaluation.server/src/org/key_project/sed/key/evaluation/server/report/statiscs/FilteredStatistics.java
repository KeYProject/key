package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;

/**
 * Filtered statics
 * @author Martin Hentschel
 */
public class FilteredStatistics {
   /**
    * The general statistics of an {@link AbstractQuestion}.
    */
   private final Map<AbstractQuestion, QuestionStatistics> questionStatistics = new HashMap<AbstractQuestion, QuestionStatistics>();

   /**
    * The tool specific statistics of an {@link AbstractQuestion}.
    */
   private final Map<Tool, Map<AbstractQuestion, QuestionStatistics>> toolQuestionStatistics = new HashMap<Tool, Map<AbstractQuestion, QuestionStatistics>>();

   /**
    * The statistics of an {@link AbstractPage}.
    */
   private final Map<AbstractPage, PageStatistics> pageStatistics = new HashMap<AbstractPage, PageStatistics>();

   /**
    * The tool specific statistics of an {@link AbstractQuestion}.
    */
   private final Map<Tool, Map<AbstractPage, PageStatistics>> toolPageStatistics = new HashMap<Tool, Map<AbstractPage, PageStatistics>>();

   /**
    * The number of included answers.
    */
   private BigInteger answersCount = BigInteger.ZERO;

   /**
    * The choice specific answers.
    */
   private final Map<AbstractChoicesQuestion, Map<Choice, ChoiceStatistics>> choiceStatistics = new HashMap<AbstractChoicesQuestion, Map<Choice, ChoiceStatistics>>();

   /**
    * Updates the statics.
    * @param questionInput The {@link QuestionInput} to analyze.
    * @param tool The optional {@link Tool}.
    */
   protected void update(QuestionInput questionInput, Tool tool) {
      if (questionInput.getValue() != null) {
         Boolean correct = questionInput.checkCorrectness();
         Integer correctnessScore = questionInput.computeCorrectnessScore();
         Integer trustScore = questionInput.computeTrustScore();
         long time = questionInput.getValueSetAt();
         long trustTime = questionInput.getTrustSetAt();
         if (correct != null || correctnessScore != null || trustScore != null || time > 0 || trustTime > 0) {
            Map<AbstractQuestion, QuestionStatistics> questionMap;
            if (tool != null) {
               questionMap = toolQuestionStatistics.get(tool);
               if (questionMap == null) {
                  questionMap = new HashMap<AbstractQuestion, QuestionStatistics>();
                  toolQuestionStatistics.put(tool, questionMap);
               }
            }
            else {
               questionMap = questionStatistics;
            }
            QuestionStatistics qs = questionMap.get(questionInput.getQuestion());
            if (qs == null) {
               qs = new QuestionStatistics();
               questionMap.put(questionInput.getQuestion(), qs);
            }
            qs.update(correct, correctnessScore, trustScore, time, trustTime);
         }
         if (questionInput.getQuestion() instanceof AbstractChoicesQuestion) {
            AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) questionInput.getQuestion();
            Map<Choice, ChoiceStatistics> statistcsMap = choiceStatistics.get(choiceQuestion);
            if (statistcsMap == null) {
               statistcsMap = new HashMap<Choice, ChoiceStatistics>();
               choiceStatistics.put(choiceQuestion, statistcsMap);
            }
            for (Choice choice : choiceQuestion.getChoices()) {
               if (questionInput.isChoiceSelected(choice)) {
                  ChoiceStatistics cs = statistcsMap.get(choice);
                  if (cs == null) {
                     cs = new ChoiceStatistics();
                     statistcsMap.put(choice, cs);
                  }
                  cs.update();
               }
            }
         }
      }
   }
   
   /**
    * Updates the statics.
    * @param pageInput The {@link AbstractPageInput} to analyze.
    * @param tool The optional {@link Tool}.
    */
   protected void update(AbstractPageInput<?> pageInput, Tool tool) {
      Map<AbstractPage, PageStatistics> toolMap;
      if (tool != null) {
         toolMap = toolPageStatistics.get(tool);
         if (toolMap == null) {
            toolMap = new HashMap<AbstractPage, PageStatistics>();
            toolPageStatistics.put(tool, toolMap);
         }
      }
      else {
         toolMap = pageStatistics;
      }
      PageStatistics qp = toolMap.get(pageInput.getPage());
      if (qp == null) {
         qp = new PageStatistics();
         toolMap.put(pageInput.getPage(), qp);
      }
      qp.update(pageInput.getShownTime());
   }
   
   /**
    * Returns the choice specific statistics of an {@link AbstractChoicesQuestion}. 
    * @param question The {@link AbstractChoicesQuestion} of interest.
    * @return The choice specific statistics of an {@link AbstractChoicesQuestion}.
    */
   public Map<Choice, ChoiceStatistics> getChoiceStatistics(AbstractChoicesQuestion question) {
      Map<Choice, ChoiceStatistics> choiceMap = choiceStatistics.get(question);
      return choiceMap != null ?
             Collections.unmodifiableMap(choiceMap) :
             null;
   }

   /**
    * Returns the {@link ChoiceStatistics} of the given {@link Choice}.
    * @param question The requested {@link AbstractChoicesQuestion}.
    * @param choice The requested {@link Choice}.
    * @return The {@link ChoiceStatistics} if available or {@code null} otherwise.
    */
   public ChoiceStatistics getChoiceStatistics(AbstractChoicesQuestion question, Choice choice) {
      Map<Choice, ChoiceStatistics> choiceMap = choiceStatistics.get(question);
      return choiceMap != null ? choiceMap.get(choice) : null;
   }
   
   /**
    * Computes the percent use of the given {@link Choice}.
    * @param question The requested {@link AbstractChoicesQuestion}.
    * @param choice The requested {@link Choice}.
    * @return The computed percent usage.
    */
   public BigInteger computeChoicePercent(AbstractChoicesQuestion question, Choice choice) {
      ChoiceStatistics cs = getChoiceStatistics(question, choice);
      if (cs != null) {
         BigInteger sum = BigInteger.ZERO;
         for (Choice currentChoice : question.getChoices()) {
            ChoiceStatistics currentCs = getChoiceStatistics(question, currentChoice);
            if (currentCs != null) {
               sum = sum.add(currentCs.getSelectedCount());
            }
         }
         return cs.getSelectedCount().multiply(BigInteger.valueOf(100)).divide(sum);
      }
      else {
         return BigInteger.ZERO;
      }
   }

   /**
    * Returns the general statistics of an {@link AbstractQuestion}.
    * @return The general statistics of an {@link AbstractQuestion}.
    */
   public Map<AbstractQuestion, QuestionStatistics> getQuestionStatistics() {
      return Collections.unmodifiableMap(questionStatistics);
   }
   
   /**
    * Returns the available {@link Tool}s.
    * @return The available {@link Tool}s.
    */
   public Set<Tool> getTools() {
      return toolQuestionStatistics.keySet();
   }
   
   /**
    * Returns the tool specific statistics of an {@link AbstractQuestion}. 
    * @param tool The {@link Tool} of interest.
    * @return The tool specific statistics of an {@link AbstractQuestion}.
    */
   public Map<AbstractQuestion, QuestionStatistics> getQuestionStatistics(Tool tool) {
      Map<AbstractQuestion, QuestionStatistics> toolMap = toolQuestionStatistics.get(tool);
      return toolMap != null ?
             Collections.unmodifiableMap(toolMap) :
             null;
   }

   /**
    * Returns the tool specific {@link QuestionStatistics} of the given {@link AbstractQuestion}.
    * @param tool The requested {@link Tool}.
    * @param question The requested {@link AbstractQuestion}.
    * @return The {@link QuestionStatistics} if available or {@code null} otherwise.
    */
   public QuestionStatistics getQuestionStatistics(Tool tool, AbstractQuestion question) {
      Map<AbstractQuestion, QuestionStatistics> map = getQuestionStatistics(tool);
      return map != null ? map.get(question) : null;
   }

   /**
    * Returns the statistics of an {@link AbstractPage}.
    * @return The statistics of an {@link AbstractPage}.
    */
   public Map<AbstractPage, PageStatistics> getPageStatistics() {
      return Collections.unmodifiableMap(pageStatistics);
   }
   
   /**
    * Returns the tool specific statistics of an {@link AbstractPage}. 
    * @param tool The {@link Tool} of interest.
    * @return The tool specific statistics of an {@link AbstractPage}.
    */
   public Map<AbstractPage, PageStatistics> getPageStatistics(Tool tool) {
      Map<AbstractPage, PageStatistics> toolMap = toolPageStatistics.get(tool);
      return toolMap != null ? 
             Collections.unmodifiableMap(toolMap) : 
             null;
   }

   /**
    * Returns the tool specific {@link PageStatistics} of the given {@link AbstractPage}.
    * @param tool The requested {@link Tool}.
    * @param page The requested {@link AbstractPage}.
    * @return The {@link PageStatistics} if available or {@code null} otherwise.
    */
   public PageStatistics getPageStatistics(Tool tool, AbstractPage page) {
      Map<AbstractPage, PageStatistics> map = getPageStatistics(tool);
      return map != null ? map.get(page) : null;
   }

   /**
    * Computes the winning {@link Tool}s in terms of correctness.
    * @param question The {@link AbstractQuestion} of interest.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public Set<Tool> computeWinningCorrectTools(AbstractQuestion question) {
      return computeWinningCorrectTools(createToolQuestionMap(question));
   }
   
   /**
    * Creates a {@link Map} containing all {@link Tool} specific {@link QuestionStatistics}.
    * @param question The {@link AbstractQuestion} of interest.
    * @return The created {@link Map}.
    */
   protected Map<Tool, QuestionStatistics> createToolQuestionMap(AbstractQuestion question) {
      Map<Tool, QuestionStatistics> questionStatistics = new HashMap<Tool, QuestionStatistics>();
      for (Tool tool : getTools()) {
         questionStatistics.put(tool, getQuestionStatistics(tool, question));
      }
      return questionStatistics;
   }
   
   /**
    * Computes the winning {@link Tool}s in terms of correctness.
    * @param questionStatistics The {@link QuestionStatistics} to analyze.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public static Set<Tool> computeWinningCorrectTools(Map<Tool, QuestionStatistics> questionStatistics) {
      BigDecimal max = BigDecimal.valueOf(-1);
      Set<Tool> maxTools = null;
      for (Entry<Tool, QuestionStatistics> entry : questionStatistics.entrySet()) {
         QuestionStatistics qs = entry.getValue();
         if (qs != null) {
            BigDecimal current = qs.computeCorrect();
            if (current.compareTo(max) > 0) {
               max = current;
               maxTools = new HashSet<Tool>();
               maxTools.add(entry.getKey());
            }
            else if (current.compareTo(max) == 0) {
               maxTools.add(entry.getKey());
            }
         }
      }
      return maxTools;
   }

   /**
    * Computes the winning {@link Tool}s in terms of trust.
    * @param question The {@link AbstractQuestion} of interest.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public Set<Tool> computeWinningCorrectTrustTools(AbstractQuestion question) {
      return computeWinningCorrectTrustTools(createToolQuestionMap(question));
   }

   
   /**
    * Computes the winning {@link Tool}s in terms of trust.
    * @param questionStatistics The {@link QuestionStatistics} to analyze.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public static Set<Tool> computeWinningCorrectTrustTools(Map<Tool, QuestionStatistics> questionStatistics) {
      BigDecimal max = BigDecimal.valueOf(-1);
      Set<Tool> maxTools = null;
      for (Entry<Tool, QuestionStatistics> entry : questionStatistics.entrySet()) {
         QuestionStatistics qs = entry.getValue();
         if (qs != null) {
            BigDecimal current = qs.computeTrustCorrect();
            if (current.compareTo(max) > 0) {
               max = current;
               maxTools = new HashSet<Tool>();
               maxTools.add(entry.getKey());
            }
            else if (current.compareTo(max) == 0) {
               maxTools.add(entry.getKey());
            }
         }
      }
      return maxTools;
   }
   

   /**
    * Computes the winning {@link Tool}s in terms of time.
    * @param question The {@link AbstractQuestion} of interest.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public Set<Tool> computeWinningTimeTools(AbstractQuestion question) {
      return computeWinningTimeTools(createToolQuestionMap(question));
   }
   
   /**
    * Computes the winning {@link Tool}s in terms of time.
    * @param questionStatistics The {@link QuestionStatistics} to analyze.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public static Set<Tool> computeWinningTimeTools(Map<Tool, QuestionStatistics> questionStatistics) {
      BigInteger min = null;
      Set<Tool> minTools = null;
      for (Entry<Tool, QuestionStatistics> entry : questionStatistics.entrySet()) {
         QuestionStatistics qs = entry.getValue();
         if (qs != null) {
            BigInteger current = qs.computeAverageTime();
            if (min == null || current.compareTo(min) < 0) {
               min = current;
               minTools = new HashSet<Tool>();
               minTools.add(entry.getKey());
            }
            else if (current.compareTo(min) == 0) {
               minTools.add(entry.getKey());
            }
         }
      }
      return minTools;
   }

   /**
    * Computes the winning {@link Tool}s in terms of trust time.
    * @param question The {@link AbstractQuestion} of interest.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public Set<Tool> computeWinningTrustTimeTools(AbstractQuestion question) {
      return computeWinningTrustTimeTools(createToolQuestionMap(question));
   }
   
   /**
    * Computes the winning {@link Tool}s in terms of trust time.
    * @param questionStatistics The {@link QuestionStatistics} to analyze.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public static Set<Tool> computeWinningTrustTimeTools(Map<Tool, QuestionStatistics> questionStatistics) {
      BigInteger min = null;
      Set<Tool> minTools = null;
      for (Entry<Tool, QuestionStatistics> entry : questionStatistics.entrySet()) {
         QuestionStatistics qs = entry.getValue();
         if (qs != null) {
            BigInteger current = qs.computeAverageTrustTime();
            if (min == null || current.compareTo(min) < 0) {
               min = current;
               minTools = new HashSet<Tool>();
               minTools.add(entry.getKey());
            }
            else if (current.compareTo(min) == 0) {
               minTools.add(entry.getKey());
            }
         }
      }
      return minTools;
   }

   /**
    * Computes the winning {@link Tool}s in terms of time.
    * @param page The {@link AbstractPage} of interest.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public Set<Tool> computeWinningPageTimeTools(AbstractPage page) {
      BigInteger min = null;
      Set<Tool> minTools = null;
      for (Tool tool : getTools()) {
         PageStatistics qs = getPageStatistics(tool, page);
         if (qs != null) {
            BigInteger current = qs.computeAverageTime();
            if (min == null || current.compareTo(min) < 0) {
               min = current;
               minTools = new HashSet<Tool>();
               minTools.add(tool);
            }
            else if (current.compareTo(min) == 0) {
               minTools.add(tool);
            }
         }
      }
      return minTools;
   }

   /**
    * Computes the winning {@link Tool}s in terms of trust score.
    * @param question The {@link AbstractQuestion} of interest.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public Set<Tool> computeWinningTrustScoreTools(AbstractQuestion question) {
      return computeWinningTrustScoreTools(createToolQuestionMap(question));
   }

   /**
    * Computes the winning {@link Tool}s in terms of trust score.
    * @param questionStatistics The {@link QuestionStatistics} to analyze.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public static Set<Tool> computeWinningTrustScoreTools(Map<Tool, QuestionStatistics> questionStatistics) {
      BigInteger max = null;
      Set<Tool> maxTools = null;
      for (Entry<Tool, QuestionStatistics> entry : questionStatistics.entrySet()) {
         QuestionStatistics qs = entry.getValue();
         if (qs != null) {
            BigInteger current = qs.computeAverageTime();
            if (max == null || current.compareTo(max) > 0) {
               max = current;
               maxTools = new HashSet<Tool>();
               maxTools.add(entry.getKey());
            }
            else if (current.compareTo(max) == 0) {
               maxTools.add(entry.getKey());
            }
         }
      }
      return maxTools;
   }

   /**
    * Returns the number of included answers.
    * @return The number of included answers.
    */
   public BigInteger getAnswersCount() {
      return answersCount;
   }

   /**
    * Increases the number of included answers by one.
    */
   protected void updateAnswersCount() {
      answersCount = answersCount.add(BigInteger.ONE);
   }

   /**
    * Computes a {@link QuestionStatistics} based on all available
    * {@link Tool} specific {@link QuestionStatistics}.
    * @param tool The {@link Tool} of interest.
    * @return The computed {@link QuestionStatistics}.
    */
   public QuestionStatistics computeAllTogetherQuestionStatistics(Tool tool) {
      BigInteger correctCount = BigInteger.ZERO;
      BigInteger wrongCount = BigInteger.ZERO;
      BigInteger scoreSum = BigInteger.ZERO;
      BigInteger correctTrustCount = BigInteger.ZERO;
      BigInteger wrongTrustCount = BigInteger.ZERO;
      BigInteger timesCount = BigInteger.ZERO;
      BigInteger timesSum = BigInteger.ZERO;
      BigInteger trustTimesCount = BigInteger.ZERO;
      BigInteger trustTimesSum = BigInteger.ZERO;
      BigInteger trustScoreSum = BigInteger.ZERO;
      Map<AbstractQuestion, QuestionStatistics> toolQuestions = getQuestionStatistics(tool);
      if (toolQuestions != null) {
         for (QuestionStatistics qs : toolQuestions.values()) {
            correctCount = correctCount.add(qs.getCorrectCount());
            wrongCount = wrongCount.add(qs.getWrongCount());
            scoreSum = scoreSum.add(qs.getScoreSum());
            correctTrustCount = correctTrustCount.add(qs.getCorrectTrustCount());
            wrongTrustCount = wrongTrustCount.add(qs.getWrongTrustCount());
            timesCount = timesCount.add(qs.getTimesCount());
            timesSum = timesSum.add(qs.getTimesSum());
            trustTimesCount = trustTimesCount.add(qs.getTrustTimesCount());
            trustTimesSum = trustTimesSum.add(qs.getTrustTimesSum());
            trustScoreSum = trustScoreSum.add(qs.getTrustScoreSum());
         }
      }
      return new QuestionStatistics(correctCount, wrongCount, scoreSum, correctTrustCount, wrongTrustCount, timesCount, timesSum, trustTimesCount, trustTimesSum, trustScoreSum);
   }
}