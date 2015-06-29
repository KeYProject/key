package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
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
    * Updates the statics.
    * @param questionInput The {@link QuestionInput} to analyze.
    * @param tool The optional {@link Tool}.
    */
   protected void update(QuestionInput questionInput, Tool tool) {
      Boolean correct = questionInput.checkCorrectness();
      Boolean correctTrust = questionInput.checkTrust();
      long time = questionInput.getValueSetAt();
      long trustTime = questionInput.getTrustSetAt();
      if (correct != null || correctTrust != null || time > 0 || trustTime > 0) {
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
         qs.update(correct, correctTrust, time, trustTime);
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
      return Collections.unmodifiableMap(toolQuestionStatistics.get(tool));
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
      return Collections.unmodifiableMap(toolPageStatistics.get(tool));
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
      BigInteger max = BigInteger.valueOf(-1);
      Set<Tool> maxTools = null;
      for (Tool tool : getTools()) {
         QuestionStatistics qs = getQuestionStatistics(tool, question);
         BigInteger current = qs.computeAverageCorrect();
         if (current.compareTo(max) > 0) {
            max = current;
            maxTools = new HashSet<Tool>();
            maxTools.add(tool);
         }
         else if (current.compareTo(max) == 0) {
            maxTools.add(tool);
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
      BigInteger max = BigInteger.valueOf(-1);
      Set<Tool> maxTools = null;
      for (Tool tool : getTools()) {
         QuestionStatistics qs = getQuestionStatistics(tool, question);
         BigInteger current = qs.computeAverageTrustCorrect();
         if (current.compareTo(max) > 0) {
            max = current;
            maxTools = new HashSet<Tool>();
            maxTools.add(tool);
         }
         else if (current.compareTo(max) == 0) {
            maxTools.add(tool);
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
      BigInteger min = null;
      Set<Tool> minTools = null;
      for (Tool tool : getTools()) {
         QuestionStatistics qs = getQuestionStatistics(tool, question);
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
      return minTools;
   }

   /**
    * Computes the winning {@link Tool}s in terms of trust time.
    * @param question The {@link AbstractQuestion} of interest.
    * @return The {@link Set} of winning {@link Tool}s.
    */
   public Set<Tool> computeWinningTrustTimeTools(AbstractQuestion question) {
      BigInteger min = null;
      Set<Tool> minTools = null;
      for (Tool tool : getTools()) {
         QuestionStatistics qs = getQuestionStatistics(tool, question);
         BigInteger current = qs.computeAverageTrustTime();
         if (min == null || current.compareTo(min) < 0) {
            min = current;
            minTools = new HashSet<Tool>();
            minTools.add(tool);
         }
         else if (current.compareTo(min) == 0) {
            minTools.add(tool);
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
      return minTools;
   }
}