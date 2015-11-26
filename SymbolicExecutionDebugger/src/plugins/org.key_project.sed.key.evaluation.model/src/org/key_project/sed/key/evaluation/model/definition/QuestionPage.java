package org.key_project.sed.key.evaluation.model.definition;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public class QuestionPage extends AbstractPage implements IPageWithWorkbenchModifier {
   private final List<AbstractQuestion> questions;

   private final IWorkbenchModifier workbenchModifier;
   
   private final boolean useForm;

   public QuestionPage(String name, String title, String message, boolean wrapLayout, boolean toolBased, IWorkbenchModifier workbenchModifier, AbstractQuestion... questions) {
      this(name, title, message, true, wrapLayout, toolBased, workbenchModifier, questions);
   }

   public QuestionPage(String name, String title, String latexTitle, String message, boolean wrapLayout, boolean toolBased, IWorkbenchModifier workbenchModifier, AbstractQuestion... questions) {
      this(name, title, latexTitle, message, true, wrapLayout, toolBased, true, workbenchModifier, CollectionUtil.toList(questions));
   }

   public QuestionPage(String name, String title, String message, boolean wrapLayout, boolean toolBased, IWorkbenchModifier workbenchModifier, List<AbstractQuestion> questions) {
      this(name, title, message, true, wrapLayout, toolBased, workbenchModifier, questions);
   }
   
   public QuestionPage(String name, String title, String message, boolean useForm, boolean wrapLayout, boolean toolBased, IWorkbenchModifier workbenchModifier, AbstractQuestion... questions) {
      this(name, title, message, useForm, wrapLayout, toolBased, workbenchModifier, CollectionUtil.toList(questions));
   }
   
   public QuestionPage(String name, String title, String latexTitle, String message, boolean useForm, boolean wrapLayout, boolean toolBased, IWorkbenchModifier workbenchModifier, AbstractQuestion... questions) {
      this(name, title, latexTitle, message, useForm, wrapLayout, toolBased, workbenchModifier, CollectionUtil.toList(questions));
   }

   public QuestionPage(String name, String title, String message, boolean useForm, boolean wrapLayout, boolean toolBased, boolean enabled, IWorkbenchModifier workbenchModifier, AbstractQuestion... questions) {
      this(name, title, message, useForm, wrapLayout, toolBased, enabled, workbenchModifier, CollectionUtil.toList(questions));
   }

   public QuestionPage(String name, String title, String message, boolean useForm, boolean wrapLayout, boolean toolBased, IWorkbenchModifier workbenchModifier, List<AbstractQuestion> questions) {
      this(name, title, message, useForm, wrapLayout, toolBased, true, workbenchModifier, questions);
   }

   public QuestionPage(String name, String title, String latexTitle, String message, boolean useForm, boolean wrapLayout, boolean toolBased, IWorkbenchModifier workbenchModifier, List<AbstractQuestion> questions) {
      this(name, title, latexTitle, message, useForm, wrapLayout, toolBased, true, workbenchModifier, questions);
   }

   public QuestionPage(String name, String title, String message, boolean useForm, boolean wrapLayout, boolean toolBased, boolean enabled, IWorkbenchModifier workbenchModifier, List<AbstractQuestion> questions) {
      this(name, title, title, message, useForm, wrapLayout, toolBased, enabled, workbenchModifier, questions);
   }

   public QuestionPage(String name, String title, String latexTitle, String message, boolean useForm, boolean wrapLayout, boolean toolBased, boolean enabled, IWorkbenchModifier workbenchModifier, List<AbstractQuestion> questions) {
      super(name, title, latexTitle, message, wrapLayout, toolBased, enabled);
      this.workbenchModifier = workbenchModifier;
      this.questions = questions;
      this.useForm = useForm;
      validateQuestions();
   }
   
   protected void validateQuestions() {
      // Ensure that all children have different names
      Set<String> usedNames = new HashSet<String>();
      if (questions != null) {
         for (AbstractQuestion question : questions) {
            if (!usedNames.add(question.getName())) {
               throw new IllegalStateException("Question name '" + question.getName() + "' used multiple times.");
            }
         }
      }
   }

   public AbstractQuestion[] getQuestions() {
      return questions.toArray(new AbstractQuestion[questions.size()]);
   }

   public AbstractQuestion getQuestion(final String name) {
      return CollectionUtil.search(questions, new IFilter<AbstractQuestion>() {
         @Override
         public boolean select(AbstractQuestion element) {
            return ObjectUtil.equals(element.getName(), name);
         }
      });
   }

   public int countQuestions() {
      return questions.size();
   }

   public IWorkbenchModifier getWorkbenchModifier() {
      return workbenchModifier;
   }

   public boolean isUseForm() {
      return useForm;
   }
}
