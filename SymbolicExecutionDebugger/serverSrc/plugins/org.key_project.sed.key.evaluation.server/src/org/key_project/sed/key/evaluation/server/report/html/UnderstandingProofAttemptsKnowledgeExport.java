package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

/**
 * Creates a CSV file with the participants experience.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsKnowledgeExport implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb) {
      AbstractForm evaluationForm = evaluation.getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME);
      AbstractForm introductionForm = evaluation.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
      QuestionPage backgroundPage = (QuestionPage) introductionForm.getPage(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
      AbstractQuestion javaQuestion = backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_JAVA_QUESTION_NAME);
      AbstractQuestion jmlQuestion = backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_JML_QUESTION_NAME);
      AbstractQuestion keyQuestion = backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
      AbstractQuestion sedQuestion = backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME);
      List<AdditionalFile> additionalFiles = new LinkedList<AdditionalFile>();
      for (IStatisticsFilter filter : statistics.getFilters()) {
         // Get knowledge
         ChoiceSummary javaSummary = new ChoiceSummary();
         ChoiceSummary jmlSummary = new ChoiceSummary();
         ChoiceSummary keySummary = new ChoiceSummary();
         ChoiceSummary sedSummary = new ChoiceSummary();
         NestedChoiceSummary key = new NestedChoiceSummary(); // Children are SED
         for (Entry<String, EvaluationAnswers> entry : result.getIdInputMap().entrySet()) {
            List<AbstractFormInput<?>> formInputs = entry.getValue().getFormInputs(evaluationForm);
            if (formInputs != null && formInputs.size() == 1) { // Otherwise form not completed or multi valued
               if (filter.accept(entry.getValue())) {
                  // Java
                  QuestionInput javaInput = entry.getValue().getQuestionInputs(javaQuestion).get(0);
                  if (UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_NON_VALUE.equals(javaInput.getValue())) {
                     javaSummary.increaseNone();
                  }
                  else if (UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_LESS_THAN_2_YEARS_VALUE.equals(javaInput.getValue())) {
                     javaSummary.increaseLess();
                  }
                  else if (UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_MORE_THAN_2_YEARS_VALUE.equals(javaInput.getValue())) {
                     javaSummary.increaseMore();
                  }
                  else {
                     throw new IllegalArgumentException("Evaluation implementation has changed.");
                  }
                  // Jml
                  QuestionInput jmlInput = entry.getValue().getQuestionInputs(jmlQuestion).get(0);
                  if (UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_NON_VALUE.equals(jmlInput.getValue())) {
                     jmlSummary.increaseNone();
                  }
                  else if (UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_LESS_THAN_2_YEARS_VALUE.equals(jmlInput.getValue())) {
                     jmlSummary.increaseLess();
                  }
                  else if (UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_MORE_THAN_2_YEARS_VALUE.equals(jmlInput.getValue())) {
                     jmlSummary.increaseMore();
                  }
                  else {
                     throw new IllegalArgumentException("Evaluation implementation has changed.");
                  }
                  // KeY
                  NestedChoiceSummary sed = null;
                  QuestionInput keyInput = entry.getValue().getQuestionInputs(keyQuestion).get(0);
                  if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE.equals(keyInput.getValue())) {
                     keySummary.increaseNone();
                     sed = key.getNone();
                  }
                  else if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE.equals(keyInput.getValue())) {
                     keySummary.increaseLess();
                     sed = key.getLess();
                  }
                  else if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE.equals(keyInput.getValue())) {
                     keySummary.increaseMore();
                     sed = key.getMore();
                  }
                  else {
                     throw new IllegalArgumentException("Evaluation implementation has changed.");
                  }
                  // SED
                  QuestionInput sedInput = entry.getValue().getQuestionInputs(sedQuestion).get(0);
                  if (UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_NON_VALUE.equals(sedInput.getValue())) {
                     sedSummary.increaseNone();
                     sed.getNone().increase();
                  }
                  else if (UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_LESS_THAN_1_YEAR_VALUE.equals(sedInput.getValue())) {
                     sedSummary.increaseLess();
                     sed.getLess().increase();
                  }
                  else if (UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_MORE_THAN_1_YEAR_VALUE.equals(sedInput.getValue())) {
                     sedSummary.increaseMore();
                     sed.getMore().increase();
                  }
                  else {
                     throw new IllegalArgumentException("Evaluation implementation has changed.");
                  }
               }
            }
         }
         // Create CSV file
         StringBuffer csv = new StringBuffer();
         csv.append("xitem, Java, JML, KeY, SED" + StringUtil.NEW_LINE);
         csv.append("None, " + javaSummary.getNone() + ", " + jmlSummary.getNone() + ", " + keySummary.getNone() + ", " + sedSummary.getNone() + StringUtil.NEW_LINE);
         csv.append("\\ $<$ $x$ years, " + javaSummary.getLess() + ", " + jmlSummary.getLess() + ", " + keySummary.getLess() + ", " + sedSummary.getLess() + StringUtil.NEW_LINE);
         csv.append("\\ $\\geq$ $x$ years, " + javaSummary.getMore() + ", " + jmlSummary.getMore() + ", " + keySummary.getMore() + ", " + sedSummary.getMore());
         additionalFiles.add(new AdditionalFile("_Knowledge_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".csv", csv.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
         // Crate Latex file
         StringBuffer latex = new StringBuffer();
         latex.append("\\begin{tabular}{lllll}" + StringUtil.NEW_LINE);
         latex.append("\\toprule" + StringUtil.NEW_LINE);
         latex.append("&&&\\SED&\\\\" + StringUtil.NEW_LINE);
         latex.append("&&None & $<$ 1 year & $\\geq$ 1 year \\\\" + StringUtil.NEW_LINE);
         latex.append("\\midrule" + StringUtil.NEW_LINE);
         latex.append("&None & " + key.getNone().getNone().getValue() + " & " + key.getNone().getLess().getValue() + " & " + key.getNone().getMore().getValue() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\KeY & $<$ 2 years & " + key.getLess().getNone().getValue() + " & " + key.getLess().getLess().getValue() + " & " + key.getLess().getMore().getValue() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("& $\\geq$ 2 years & " + key.getMore().getNone().getValue() + " & " + key.getMore().getLess().getValue() + " & " + key.getMore().getMore().getValue() + "\\\\" + StringUtil.NEW_LINE);
         
         latex.append("\\bottomrule" + StringUtil.NEW_LINE);
         latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
         additionalFiles.add(new AdditionalFile("_Knowledge_KeY_SED_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", latex.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      }
      return additionalFiles;
   }
   
   private static class NestedChoiceSummary {
      private NestedChoiceSummary none;
      private NestedChoiceSummary less;
      private NestedChoiceSummary more;
      
      private BigInteger value = BigInteger.ZERO;
      
      public NestedChoiceSummary getNone() {
         if (none == null) {
            none = new NestedChoiceSummary();
         }
         return none;
      }

      public NestedChoiceSummary getLess() {
         if (less == null) {
            less = new NestedChoiceSummary();
         }
         return less;
      }

      public NestedChoiceSummary getMore() {
         if (more == null) {
            more = new NestedChoiceSummary();
         }
         return more;
      }

      public BigInteger getValue() {
         return value;
      }

      public void increase() {
         value = value.add(BigInteger.ONE);
      }
   }
   
   /**
    * Utility class to count the experience of participants.
    * @author Martin Hentschel
    */
   private static class ChoiceSummary {
      /**
       * The counted occurrence of experience: none
       */
      private BigInteger none = BigInteger.ZERO;
      
      /**
       * The counted occurrence of experience: less x years
       */
      private BigInteger less = BigInteger.ZERO;
      
      /**
       * The counted occurrence of experience: more or equal x years
       */
      private BigInteger more = BigInteger.ZERO;

      /**
       * Returns the counted occurrence of experience: none
       * @return The counted occurrence of experience: none
       */
      public BigInteger getNone() {
         return none;
      }

      /**
       * Returns the counted occurrence of experience: less x years
       * @return The counted occurrence of experience: less x years
       */
      public BigInteger getLess() {
         return less;
      }

      /**
       * Returns the counted occurrence of experience: more or equal x years
       * @return The counted occurrence of experience: more or equal x years
       */
      public BigInteger getMore() {
         return more;
      }
      
      /**
       * Increases the experience by {@code 1}.
       */
      public void increaseNone() {
         none = none.add(BigInteger.ONE);
      }

      /**
       * Increases the experience by {@code 1}.
       */
      public void increaseLess() {
         less = less.add(BigInteger.ONE);
      }

      /**
       * Increases the experience by {@code 1}.
       */
      public void increaseMore() {
         more = more.add(BigInteger.ONE);
      }
   }
}
