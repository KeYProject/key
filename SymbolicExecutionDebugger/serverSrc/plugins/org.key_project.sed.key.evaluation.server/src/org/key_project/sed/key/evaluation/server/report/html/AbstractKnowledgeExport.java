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
 * Provides the basic functionality to export participants knowledge.
 * @author Martin Hentschel
 */
public abstract class AbstractKnowledgeExport implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb) {
      AbstractForm evaluationForm = getEvaluationForm(evaluation);
      QuestionDefinition[] questions = getQuestions(evaluation);
      List<AdditionalFile> additionalFiles = new LinkedList<AdditionalFile>();
      for (IStatisticsFilter filter : statistics.getFilters()) {
         // Get knowledge
         ChoiceSummary[] summaries = new ChoiceSummary[questions.length];
         for (int i = 0; i < summaries.length; i++) {
            summaries[i] = new ChoiceSummary();
         }
         NestedChoiceSummary root = new NestedChoiceSummary();
         for (Entry<String, EvaluationAnswers> entry : result.getIdInputMap().entrySet()) {
            List<AbstractFormInput<?>> formInputs = entry.getValue().getFormInputs(evaluationForm);
            if (formInputs != null && formInputs.size() == 1) { // Otherwise form not completed or multi valued
               if (filter.accept(entry.getValue())) {
                  NestedChoiceSummary current = root;
                  for (int i = 0; i < summaries.length; i++) {
                     QuestionInput qi = entry.getValue().getQuestionInputs(questions[i].getQuestion()).get(0);
                     if (questions[i].getNoneValue().equals(qi.getValue())) {
                        summaries[i].increaseNone();
                        current = updateNestedChoiceNone(current, qi);
                     }
                     else if (questions[i].getLessValue().equals(qi.getValue())) {
                        summaries[i].increaseLess();
                        current = updateNestedChoiceLess(current, qi);
                     }
                     else if (questions[i].getMoreValue().equals(qi.getValue())) {
                        summaries[i].increaseMore();
                        current = updateNestedChoiceMore(current, qi);
                     }
                     else {
                        throw new IllegalArgumentException("Evaluation implementation has changed.");
                     }
                  }
                  current.increase();
               }
            }
         }
         // Create CSV file
         StringBuffer csv = new StringBuffer();
         csv.append("xitem");
         for (int i = 0; i < summaries.length; i++) {
            csv.append(", ");
            csv.append(questions[i].getColumnName());
         }
         csv.append(StringUtil.NEW_LINE);
         
         csv.append("None, ");
         for (int i = 0; i < summaries.length; i++) {
            if (i > 0) {
               csv.append(", ");
            }
            csv.append(summaries[i].getNone());
         }
         csv.append(StringUtil.NEW_LINE);

         csv.append("\\ $<$ $x$ years, ");
         for (int i = 0; i < summaries.length; i++) {
            if (i > 0) {
               csv.append(", ");
            }
            csv.append(summaries[i].getLess());
         }
         csv.append(StringUtil.NEW_LINE);
         
         csv.append("\\ $\\geq$ $x$ years, ");
         for (int i = 0; i < summaries.length; i++) {
            if (i > 0) {
               csv.append(", ");
            }
            csv.append(summaries[i].getMore());
         }
         csv.append(StringUtil.NEW_LINE);
         additionalFiles.add(new AdditionalFile("_Knowledge_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".csv", csv.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
         // Crate Latex file if needed
         String latexFileName = computeLatexFileName(filter);
         if (!StringUtil.isEmpty(latexFileName)) {
            StringBuffer latex = new StringBuffer();
            latex.append("\\begin{tabular}{lllll}" + StringUtil.NEW_LINE);
            latex.append("\\toprule" + StringUtil.NEW_LINE);
            latex.append("&&&" + getNestedChoiceColumnHeader() + "&\\\\" + StringUtil.NEW_LINE);
            latex.append("&&None & $<$ 1 year & $\\geq$ 1 year \\\\" + StringUtil.NEW_LINE);
            latex.append("\\midrule" + StringUtil.NEW_LINE);
            latex.append("&None & " + root.getNone().getNone().getValue() + " & " + root.getNone().getLess().getValue() + " & " + root.getNone().getMore().getValue() + "\\\\" + StringUtil.NEW_LINE);
            latex.append(getNestedChoiceRowHeader() + " & $<$ 2 years & " + root.getLess().getNone().getValue() + " & " + root.getLess().getLess().getValue() + " & " + root.getLess().getMore().getValue() + "\\\\" + StringUtil.NEW_LINE);
            latex.append("& $\\geq$ 2 years & " + root.getMore().getNone().getValue() + " & " + root.getMore().getLess().getValue() + " & " + root.getMore().getMore().getValue() + "\\\\" + StringUtil.NEW_LINE);
            
            latex.append("\\bottomrule" + StringUtil.NEW_LINE);
            latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
            additionalFiles.add(new AdditionalFile(latexFileName, latex.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
         }
      }
      return additionalFiles;
   }
   
   protected abstract String getNestedChoiceColumnHeader();

   protected abstract String getNestedChoiceRowHeader();

   protected abstract AbstractForm getEvaluationForm(AbstractEvaluation evaluation);
   
   protected abstract QuestionDefinition[] getQuestions(AbstractEvaluation evaluation);
   
   protected static class QuestionDefinition {
      private final AbstractQuestion question;
      private final String noneValue;
      private final String lessValue;
      private final String moreValue;
      private final String columnName;
      
      public QuestionDefinition(AbstractQuestion question, String noneValue, String lessValue, String moreValue, String columnName) {
         this.question = question;
         this.noneValue = noneValue;
         this.lessValue = lessValue;
         this.moreValue = moreValue;
         this.columnName = columnName;
      }

      public AbstractQuestion getQuestion() {
         return question;
      }

      public String getNoneValue() {
         return noneValue;
      }

      public String getLessValue() {
         return lessValue;
      }

      public String getMoreValue() {
         return moreValue;
      }

      public String getColumnName() {
         return columnName;
      }
   }
   
   protected NestedChoiceSummary updateNestedChoiceNone(NestedChoiceSummary current, QuestionInput qi) {
      return current;
   }
   
   protected NestedChoiceSummary updateNestedChoiceLess(NestedChoiceSummary current, QuestionInput qi) {
      return current;
   }
   
   protected NestedChoiceSummary updateNestedChoiceMore(NestedChoiceSummary current, QuestionInput qi) {
      return current;
   }
   
   protected String computeLatexFileName(IStatisticsFilter filter) {
      return null;
   }
   
   protected static class NestedChoiceSummary {
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
   protected static class ChoiceSummary {
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
