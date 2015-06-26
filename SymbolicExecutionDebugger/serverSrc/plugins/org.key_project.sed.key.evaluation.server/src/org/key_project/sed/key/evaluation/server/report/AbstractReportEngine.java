package org.key_project.sed.key.evaluation.server.report;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

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
               EvaluationInput fileInput = EvaluationInputReader.parse(new FileInputStream(file));
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
    * Provides the results of an evaluation.
    * @author Martin Hentschel
    */
   public static class EvaluationResult {
      /**
       * The available {@link EvaluationAnswers}.
       */
      private final Map<String, EvaluationAnswers> idInputMap = new HashMap<String, EvaluationAnswers>();

      /**
       * Analyzes the given {@link EvaluationInput}.
       * @param form The {@link AbstractFormInput} to analyze.
       * @param input The {@link EvaluationInput} to anaylze.
       */
      protected void addEvaluationInput(AbstractForm form, EvaluationInput input) {
         assert !StringUtil.isTrimmedEmpty(input.getUUID());
         EvaluationAnswers answers = idInputMap.get(input.getUUID());
         if (answers == null) {
            answers = new EvaluationAnswers();
            idInputMap.put(input.getUUID(), answers);
         }
         answers.addFormInput(input.getFormInput(form));
      }

      /**
       * Returns the available {@link EvaluationAnswers}.
       * @return The available {@link EvaluationAnswers}.
       */
      public Map<String, EvaluationAnswers> getIdInputMap() {
         return idInputMap;
      }
   }
   
   /**
    * The {@link EvaluationAnswers} grouping related {@link EvaluationInput}s.
    * @author Martin Hentschel
    */
   public static class EvaluationAnswers {
      /**
       * The available {@link QuestionInput}s.
       */
      private final Map<AbstractQuestion, List<QuestionInput>> questionMap = new HashMap<AbstractQuestion, List<QuestionInput>>();

      /**
       * The available {@link AbstractPageInput}s.
       */
      private final Map<AbstractPage, List<AbstractPageInput<?>>> pageMap = new HashMap<AbstractPage, List<AbstractPageInput<?>>>();

      /**
       * Analyzes the given {@link AbstractFormInput}.
       * @param formInput The {@link AbstractFormInput} to analyze.
       */
      protected void addFormInput(AbstractFormInput<?> formInput) {
         for (AbstractPageInput<?> pageInput : formInput.getPageInputs()) {
            if (!pageInput.getPage().isReadonly()) {
               List<AbstractPageInput<?>> pages = pageMap.get(pageInput.getPage());
               if (pages == null) {
                  pages = new LinkedList<AbstractPageInput<?>>();
                  pageMap.put(pageInput.getPage(), pages);
               }
               pages.add(pageInput);
               if (pageInput instanceof QuestionPageInput) {
                  QuestionPageInput qpi = (QuestionPageInput) pageInput;
                  for (QuestionInput questionInput : qpi.getQuestionInputs()) {
                     addQuestionInput(questionInput);
                  }
               }
               else {
                  throw new IllegalStateException("Unsupported page input:" + pageInput);
               }
            }
         }
      }

      /**
       * Analyzes the given {@link QuestionInput}.
       * @param questionInput The {@link QuestionInput} to analyze.
       */
      protected void addQuestionInput(QuestionInput questionInput) {
         if (questionInput.getQuestion().isEditable()) {
            List<QuestionInput> answers = questionMap.get(questionInput.getQuestion());
            if (answers == null) {
               answers = new LinkedList<QuestionInput>();
               questionMap.put(questionInput.getQuestion(), answers);
            }
            answers.add(questionInput);
         }
         if (questionInput.hasChoiceInputs()) {
            for (Choice choice : questionInput.getChoices()) {
               QuestionInput[] choiceInputs = questionInput.getChoiceInputs(choice);
               for (QuestionInput choiceInput : choiceInputs) {
                  addQuestionInput(choiceInput);
               }
            }
         }
         if (questionInput.countChildInputs() > 0) {
            for (QuestionInput childInput : questionInput.getChildInputs()) {
               addQuestionInput(childInput);
            }
         }
      }

      /**
       * Returns the available {@link QuestionInput} of the given {@link AbstractQuestion}.
       * @param question The requested {@link AbstractQuestion}.
       * @return The available {@link QuestionInput}s or {@code null} if none are available.
       */
      public List<QuestionInput> getQuestionInputs(AbstractQuestion question) {
         return questionMap.get(question);
      }

      /**
       * Returns the available {@link AbstractPageInput} of the given {@link AbstractPage}.
       * @param question The requested {@link AbstractQuestion}.
       * @return The available {@link AbstractPageInput}s or {@code null} if none are available.
       */
      public List<AbstractPageInput<?>> getPageInputs(AbstractPage page) {
         return pageMap.get(page);
      }
      
      /**
       * Checks if multiple values occur.
       * @return {@code true} multiple values occur, {@code false} otherwise.
       */
      public boolean hasMultipleValues() {
         return CollectionUtil.search(pageMap.values(), new IFilter<List<AbstractPageInput<?>>>() {
            @Override
            public boolean select(List<AbstractPageInput<?>> element) {
               return element != null && element.size() > 1;
            }
         }) != null;
      }
   }
}
