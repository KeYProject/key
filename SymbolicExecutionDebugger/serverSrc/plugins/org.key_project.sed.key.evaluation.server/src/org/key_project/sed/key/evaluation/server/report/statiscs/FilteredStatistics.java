package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.util.Collections;
import java.util.HashMap;
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
   private final Map<Tool, Map<AbstractQuestion, QuestionStatistics>> toolStatistics = new HashMap<Tool, Map<AbstractQuestion, QuestionStatistics>>();

   /**
    * The statistics of an {@link AbstractPage}.
    */
   private final Map<AbstractPage, PageStatistics> pageStatistics = new HashMap<AbstractPage, PageStatistics>();
   
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
            questionMap = toolStatistics.get(tool);
            if (questionMap == null) {
               questionMap = new HashMap<AbstractQuestion, QuestionStatistics>();
               toolStatistics.put(tool, questionMap);
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
    */
   protected void update(AbstractPageInput<?> pageInput) {
      PageStatistics qp = pageStatistics.get(pageInput.getPage());
      if (qp == null) {
         qp = new PageStatistics();
         pageStatistics.put(pageInput.getPage(), qp);
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
      return toolStatistics.keySet();
   }
   
   /**
    * Returns the tool specific statistics of an {@link AbstractQuestion}. 
    * @param tool The {@link Tool} of interest.
    * @return The tool specific statistics of an {@link AbstractQuestion}.
    */
   public Map<AbstractQuestion, QuestionStatistics> getQuestionStatistics(Tool tool) {
      return Collections.unmodifiableMap(toolStatistics.get(tool));
   }

   /**
    * Returns the statistics of an {@link AbstractPage}.
    * @return The statistics of an {@link AbstractPage}.
    */
   public Map<AbstractPage, PageStatistics> getPageStatistics() {
      return Collections.unmodifiableMap(pageStatistics);
   }
}