package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.ChoiceStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.FilteredStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

/**
 * Creates a CSV file with the participants experience.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsKnowledgeCSVExport implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb) {
      
      // TODO: Consider only participants who completed the evaluation!
      
      List<AdditionalFile> additionalFiles = new LinkedList<AdditionalFile>();
      for (IStatisticsFilter filter : statistics.getFilters()) {
         // Get knowledge
         ChoiceSummary javaSummary = new ChoiceSummary();
         ChoiceSummary jmlSummary = new ChoiceSummary();
         ChoiceSummary keySummary = new ChoiceSummary();
         ChoiceSummary sedSummary = new ChoiceSummary();
         FilteredStatistics fs = statistics.getFilteredStatistics(filter);
         QuestionPage backgroundPage = (QuestionPage) evaluation.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME).getPage(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
         for (AbstractQuestion question : backgroundPage.getQuestions()) {
            if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_JAVA_QUESTION_NAME.equals(question.getName())) {
               Map<Choice, ChoiceStatistics> cs = fs.getChoiceStatistics((AbstractChoicesQuestion) question);
               for (Entry<Choice, ChoiceStatistics> entry : cs.entrySet()) {
                  if (UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_NON_VALUE.equals(entry.getKey().getValue())) {
                     javaSummary.setNone(entry.getValue().getSelectedCount());
                  }
                  else if (UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_LESS_THAN_2_YEARS_VALUE.equals(entry.getKey().getValue())) {
                     javaSummary.setLess(entry.getValue().getSelectedCount());
                  }
                  else if (UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_MORE_THAN_2_YEARS_VALUE.equals(entry.getKey().getValue())) {
                     javaSummary.setMore(entry.getValue().getSelectedCount());
                  }
                  else {
                     throw new IllegalArgumentException("Evaluation implementation has changed.");
                  }
               }
            }
            else if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_JML_QUESTION_NAME.equals(question.getName())) {
               Map<Choice, ChoiceStatistics> cs = fs.getChoiceStatistics((AbstractChoicesQuestion) question);
               for (Entry<Choice, ChoiceStatistics> entry : cs.entrySet()) {
                  if (UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_NON_VALUE.equals(entry.getKey().getValue())) {
                     jmlSummary.setNone(entry.getValue().getSelectedCount());
                  }
                  else if (UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_LESS_THAN_2_YEARS_VALUE.equals(entry.getKey().getValue())) {
                     jmlSummary.setLess(entry.getValue().getSelectedCount());
                  }
                  else if (UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_MORE_THAN_2_YEARS_VALUE.equals(entry.getKey().getValue())) {
                     jmlSummary.setMore(entry.getValue().getSelectedCount());
                  }
                  else {
                     throw new IllegalArgumentException("Evaluation implementation has changed.");
                  }
               }
            }
            else if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME.equals(question.getName())) {
               Map<Choice, ChoiceStatistics> cs = fs.getChoiceStatistics((AbstractChoicesQuestion) question);
               for (Entry<Choice, ChoiceStatistics> entry : cs.entrySet()) {
                  if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE.equals(entry.getKey().getValue())) {
                     keySummary.setNone(entry.getValue().getSelectedCount());
                  }
                  else if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE.equals(entry.getKey().getValue())) {
                     keySummary.setLess(entry.getValue().getSelectedCount());
                  }
                  else if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE.equals(entry.getKey().getValue())) {
                     keySummary.setMore(entry.getValue().getSelectedCount());
                  }
                  else {
                     throw new IllegalArgumentException("Evaluation implementation has changed.");
                  }
               }
            }
            else if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME.equals(question.getName())) {
               Map<Choice, ChoiceStatistics> cs = fs.getChoiceStatistics((AbstractChoicesQuestion) question);
               for (Entry<Choice, ChoiceStatistics> entry : cs.entrySet()) {
                  if (UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_NON_VALUE.equals(entry.getKey().getValue())) {
                     sedSummary.setNone(entry.getValue().getSelectedCount());
                  }
                  else if (UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_LESS_THAN_1_YEAR_VALUE.equals(entry.getKey().getValue())) {
                     sedSummary.setLess(entry.getValue().getSelectedCount());
                  }
                  else if (UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_MORE_THAN_1_YEAR_VALUE.equals(entry.getKey().getValue())) {
                     sedSummary.setMore(entry.getValue().getSelectedCount());
                  }
                  else {
                     throw new IllegalArgumentException("Evaluation implementation has changed.");
                  }
               }
            }
            else {
               throw new IllegalArgumentException("Evaluation implementation has changed.");
            }
         }
         // Create CSV file
         StringBuffer csv = new StringBuffer();
         csv.append("xitem, Java, JML, KeY, SED" + StringUtil.NEW_LINE);
         csv.append("None, " + javaSummary.getNone() + ", " + jmlSummary.getNone() + ", " + keySummary.getNone() + ", " + sedSummary.getNone() + StringUtil.NEW_LINE);
         csv.append("\\ $<$ $x$ years, " + javaSummary.getLess() + ", " + jmlSummary.getLess() + ", " + keySummary.getLess() + ", " + sedSummary.getLess() + StringUtil.NEW_LINE);
         csv.append("\\ $\\geq$ $x$ years, " + javaSummary.getMore() + ", " + jmlSummary.getMore() + ", " + keySummary.getMore() + ", " + sedSummary.getMore());
         additionalFiles.add(new AdditionalFile("_Knowledge_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".csv", csv.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      }
      return additionalFiles;
   }
   
   private static class ChoiceSummary {
      private BigInteger none;
      
      private BigInteger less;
      
      private BigInteger more;

      public BigInteger getNone() {
         return none;
      }

      public void setNone(BigInteger none) {
         this.none = none;
      }

      public BigInteger getLess() {
         return less;
      }

      public void setLess(BigInteger less) {
         this.less = less;
      }

      public BigInteger getMore() {
         return more;
      }

      public void setMore(BigInteger more) {
         this.more = more;
      }
   }
}
