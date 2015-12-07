package org.key_project.sed.key.evaluation.server.report;

import java.io.File;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.server.report.html.HTMLAnswersSectionAppender;
import org.key_project.sed.key.evaluation.server.report.html.HTMLChoiceSectionAppender;
import org.key_project.sed.key.evaluation.server.report.html.HTMLHypotheses;
import org.key_project.sed.key.evaluation.server.report.html.HTMLToolSectionAppender;
import org.key_project.sed.key.evaluation.server.report.html.HTMLUnderstandingProofAttemptsBalancingSectionAppender;
import org.key_project.sed.key.evaluation.server.report.html.IHTMLSectionAppender;
import org.key_project.sed.key.evaluation.server.report.html.ReviewingCodeExpectedAnswersComparison;
import org.key_project.sed.key.evaluation.server.report.html.ReviewingCodeHelpfulnessExport;
import org.key_project.sed.key.evaluation.server.report.html.ReviewingCodeKnowledgeExport;
import org.key_project.sed.key.evaluation.server.report.html.ReviewingCodeSummaryExport;
import org.key_project.sed.key.evaluation.server.report.html.UnderstandingProofAttemptsExpectedAnswersComparison;
import org.key_project.sed.key.evaluation.server.report.html.UnderstandingProofAttemptsKnowledgeExport;
import org.key_project.sed.key.evaluation.server.report.html.UnderstandingProofAttemptsSummaryExport;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.CollectionUtil;

/**
 * A report engine which generates HTML reports.
 * @author Martin Hentschel
 */
public class HTMLReportEngine extends AbstractReportEngine {
   /**
    * Constructor.
    * @param storageLocation The file storage.
    */
   public HTMLReportEngine(File storageLocation) {
      super(storageLocation);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ReportContent createReport(AbstractEvaluation evaluation) throws Exception {
      // List reports
      Map<AbstractForm, List<EvaluationInput>> formInputs = listForms(evaluation);
      // Analyze reports
      EvaluationResult result = analyzeReports(formInputs);
      if (!formInputs.isEmpty()) {
         List<AdditionalFile> additionalFiles = new LinkedList<AdditionalFile>();
         // Create HTML report
         StringBuffer sb = new StringBuffer();
         sb.append("<html>");
         sb.append("<head>");
         sb.append("<title>");
         sb.append(evaluation.getName());
         sb.append("</title>");
         sb.append("</head>");
         sb.append("<body>");
         Statistics statistics = computeStatistics(evaluation, result);
         List<IHTMLSectionAppender> sectionAppender = getSectionAppender(evaluation);
         for (IHTMLSectionAppender current : sectionAppender) {
            Collection<AdditionalFile> sectionFiles = current.appendSection(getStorageLocation(), evaluation, result, statistics, sb);
            if (!CollectionUtil.isEmpty(sectionFiles)) {
               additionalFiles.addAll(sectionFiles);
            }
         }
         sb.append("</body>");
         sb.append("</html>");
         return new ReportContent(sb.toString(), additionalFiles);
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the available {@link IHTMLSectionAppender} of the given {@link AbstractEvaluation}.
    * @param evaluation The requested {@link AbstractEvaluation}.
    * @return The available {@link IHTMLSectionAppender}.
    */
   public List<IHTMLSectionAppender> getSectionAppender(AbstractEvaluation evaluation) {
      List<IHTMLSectionAppender> result = new LinkedList<IHTMLSectionAppender>();
      result.add(new HTMLHypotheses());
      result.add(new HTMLToolSectionAppender());
      result.add(new HTMLChoiceSectionAppender());
      if (evaluation instanceof UnderstandingProofAttemptsEvaluation) {
         result.add(new UnderstandingProofAttemptsKnowledgeExport());
         result.add(new UnderstandingProofAttemptsSummaryExport());
         result.add(new HTMLUnderstandingProofAttemptsBalancingSectionAppender());
         result.add(new UnderstandingProofAttemptsExpectedAnswersComparison());
      }
      else if (evaluation instanceof ReviewingCodeEvaluation) {
         result.add(new ReviewingCodeKnowledgeExport());
         result.add(new ReviewingCodeSummaryExport());
         result.add(new ReviewingCodeHelpfulnessExport());
         result.add(new ReviewingCodeExpectedAnswersComparison());
      }
      result.add(new HTMLAnswersSectionAppender());
      return result;
   }
}
