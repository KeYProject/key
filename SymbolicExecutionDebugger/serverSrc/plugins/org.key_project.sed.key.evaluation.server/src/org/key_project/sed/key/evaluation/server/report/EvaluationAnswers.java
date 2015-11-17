package org.key_project.sed.key.evaluation.server.report;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

/**
 * The {@link EvaluationAnswers} grouping related {@link EvaluationInput}s.
 * @author Martin Hentschel
 */
public class EvaluationAnswers {
   /**
    * The available {@link QuestionInput}s.
    */
   private final Map<AbstractQuestion, List<QuestionInput>> questionMap = new HashMap<AbstractQuestion, List<QuestionInput>>();

   /**
    * The available {@link AbstractPageInput}s.
    */
   private final Map<AbstractPage, List<AbstractPageInput<?>>> pageMap = new HashMap<AbstractPage, List<AbstractPageInput<?>>>();

   /**
    * The available {@link AbstractFormInput}s.
    */
   private final Map<AbstractForm, List<AbstractFormInput<?>>> formMap = new HashMap<AbstractForm, List<AbstractFormInput<?>>>();

   /**
    * The used {@link Tool}s per {@link AbstractPage}.
    */
   private final Map<AbstractPage, List<Tool>> pageToolMap = new HashMap<AbstractPage, List<Tool>>();
   
   /**
    * Analyzes the given {@link AbstractFormInput}.
    * @param formInput The {@link AbstractFormInput} to analyze.
    */
   protected void addFormInput(AbstractFormInput<?> formInput) {
      List<AbstractFormInput<?>> forms = formMap.get(formInput.getForm());
      if (forms == null) {
         forms = new LinkedList<AbstractFormInput<?>>();
         formMap.put(formInput.getForm(), forms);
      }
      forms.add(formInput);      
      // Analyze pages
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
      // Analyze defined tools
      for (AbstractFormInput<?> afi : formInput.getEvaluationInput().getFormInputs()) {
         if (afi instanceof RandomFormInput) {
            RandomFormInput rfi = (RandomFormInput) afi;
            for (AbstractPageInput<?> toolPage : rfi.getToolPages()) {
               Tool tool = rfi.getTool(toolPage);
               if (tool != null) {
                  List<Tool> toolList = pageToolMap.get(toolPage.getPage());
                  if (toolList == null) {
                     toolList = new LinkedList<Tool>();
                     pageToolMap.put(toolPage.getPage(), toolList);
                  }
                  toolList.add(tool);
               }
            }
         }
      }
   }

   /**
    * Analyzes the given {@link QuestionInput}.
    * @param questionInput The {@link QuestionInput} to analyze.
    */
   protected void addQuestionInput(QuestionInput questionInput) {
      if (questionInput.getQuestion().isEditable() && questionInput.getQuestion().isEnabled()) {
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
    * Returns all available {@link AbstractForm}s.
    * @return The available {@link AbstractForm}s.
    */
   public Set<AbstractForm> getForms() {
      return formMap.keySet();
   }

   /**
    * Returns the available {@link AbstractFormInput} of the given {@link AbstractForm}.
    * @param form The requested {@link AbstractForm}.
    * @return The available {@link AbstractFormInput}s or {@code null} if none are available.
    */
   public List<AbstractFormInput<?>> getFormInputs(AbstractForm form) {
      return formMap.get(form);
   }
   
   /**
    * Returns all available {@link AbstractQuestion}s.
    * @return The available {@link AbstractQuestion}s.
    */
   public Set<AbstractQuestion> getQuestions() {
      return questionMap.keySet();
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
    * Returns all available {@link AbstractPage}s.
    * @return The available {@link AbstractPage}s.
    */
   public Set<AbstractPage> getPages() {
      return pageMap.keySet();
   }

   /**
    * Returns the available {@link AbstractPageInput} of the given {@link AbstractPage}.
    * @param page The requested {@link AbstractPage}.
    * @return The available {@link AbstractPageInput}s or {@code null} if none are available.
    */
   public List<AbstractPageInput<?>> getPageInputs(AbstractPage page) {
      return pageMap.get(page);
   }

   /**
    * Returns the available {@link Tool} of the given {@link AbstractPage}.
    * @param page The requested {@link AbstractPage}.
    * @return The available {@link Tool}s or {@code null} if none are available.
    */
   public List<Tool> getTools(AbstractPage page) {
      return pageToolMap.get(page);
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