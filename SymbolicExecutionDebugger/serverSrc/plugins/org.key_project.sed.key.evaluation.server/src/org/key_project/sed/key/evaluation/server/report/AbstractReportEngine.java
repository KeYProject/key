package org.key_project.sed.key.evaluation.server.report;

import java.io.File;
import java.io.FileOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.sed.key.evaluation.server.report.filter.AllStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.filter.UnderstandingProofAttemptsKeYExperienceFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IOUtil;

/**
 * Provides the basic functionality to generate reports.
 * @author Martin Hentschel
 */
public abstract class AbstractReportEngine {
   /**
    * The file storage.
    */
   private final File storageLocation;
   
   /**
    * Constructor.
    * @param storageLocation The file storage.
    */
   public AbstractReportEngine(File storageLocation) {
      this.storageLocation = storageLocation;
   }
   
   /**
    * Saves the generated report at the given target {@link File}.
    * @param evaluation The {@link AbstractEvaluation} to generate report for.
    * @param target The target {@link File} to save report at.
    * @return {@code true} report created, {@link false} no report created because no results are available.
    * @throws Exception Occurred Exception.
    */
   public boolean saveReport(AbstractEvaluation evaluation, File target) throws Exception {
      String report = createReport(evaluation);
      if (report != null) {
         IOUtil.writeTo(new FileOutputStream(target), report);
         return true;
      }
      else {
         return false;
      }
   }

   /**
    * Creates the report of the given {@link AbstractEvaluation}.
    * @param evaluation The {@link AbstractEvaluation} to generate report for.
    * @return The created report or {@code null} if no results are available.
    * @throws Exception Occurred Exception.
    */
   public abstract String createReport(AbstractEvaluation evaluation) throws Exception;
   
   /**
    * Lists all available {@link EvaluationInput}s.
    * @param evaluation The {@link AbstractEvaluation} to generate report for.
    * @return The available {@link EvaluationInput}s. 
    * @throws Exception Occurred Exception.
    */
   protected Map<AbstractForm, List<EvaluationInput>> listForms(AbstractEvaluation evaluation) throws Exception {
      Map<AbstractForm, List<EvaluationInput>> result = new HashMap<AbstractForm, List<EvaluationInput>>();
      for (AbstractForm form : evaluation.getForms()) {
         File[] files = FileStorage.listFormFiles(storageLocation, evaluation.getName(), form.getName());
         if (!ArrayUtil.isEmpty(files)) {
            List<EvaluationInput> list = new ArrayList<EvaluationInput>(files.length);
            result.put(form, list);
            for (File file : files) {
               EvaluationInput fileInput = EvaluationInputReader.parse(file);
               list.add(fileInput);
            }
         }
      }
      return result;
   }
   
   /**
    * Analyzes the available {@link EvaluationInput}s.
    * @param formInputs The {@link EvaluationInput}s to analyze.
    * @return The created {@link EvaluationResult}.
    */
   protected EvaluationResult analyzeReports(Map<AbstractForm, List<EvaluationInput>> formInputs) {
      EvaluationResult result = new EvaluationResult();
      for (Entry<AbstractForm, List<EvaluationInput>> entry : formInputs.entrySet()) {
         for (EvaluationInput input : entry.getValue()) {
            result.addEvaluationInput(entry.getKey(), input);
         }
      }
      return result;
   }
   
   /**
    * Computes {@link Statistics} based on the given {@link EvaluationResult}.
    * @param evaluation The {@link AbstractEvaluation} for which the report is created.
    * @param result The available {@link EvaluationResult}s.
    * @return The computed {@link Statistics}.
    */
   protected Statistics computeStatistics(AbstractEvaluation evaluation, 
                                          EvaluationResult result) {
      IStatisticsFilter[] filters = getFilters(evaluation);
      return new Statistics(filters, result);
   }
   
   /**
    * Returns all available {@link IStatisticsFilter} for the given {@link AbstractEvaluation}.
    * @param evaluation The {@link AbstractEvaluation} for which {@link IStatisticsFilter} are requested.
    * @return The available {@link IStatisticsFilter}s.
    */
   protected IStatisticsFilter[] getFilters(AbstractEvaluation evaluation) {
      if (evaluation instanceof UnderstandingProofAttemptsEvaluation) {
         List<IStatisticsFilter> filters = new LinkedList<IStatisticsFilter>();
         filters.add(new AllStatisticsFilter());
         AbstractForm introductionForm = evaluation.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
         QuestionPage backgroundPage = (QuestionPage) introductionForm.getPage(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
         RadioButtonsQuestion keyQuestion = (RadioButtonsQuestion) backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
         for (Choice choice : keyQuestion.getChoices()) {
            filters.add(new UnderstandingProofAttemptsKeYExperienceFilter(choice));
         }
         return filters.toArray(new IStatisticsFilter[filters.size()]);
      }
      else {
         return new IStatisticsFilter[] {new AllStatisticsFilter()};
      }
   }

   /**
    * Returns the analyzed storage location.
    * @return The analyzed storage location.
    */
   public File getStorageLocation() {
      return storageLocation;
   }
}
