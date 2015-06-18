package org.key_project.sed.key.evaluation.model.definition;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public class QuestionPage extends AbstractPage {
   private final List<AbstractQuestion> questions;

   private final IWorkbenchModifier workbenchModifier;
   
   public QuestionPage(String name, String title, String message, boolean wrapLayout, IWorkbenchModifier workbenchModifier, AbstractQuestion... questions) {
      this(name, title, message, wrapLayout, workbenchModifier, CollectionUtil.toList(questions));
   }

   public QuestionPage(String name, String title, String message, boolean wrapLayout, IWorkbenchModifier workbenchModifier, List<AbstractQuestion> questions) {
      super(name, title, message, wrapLayout);
      this.workbenchModifier = workbenchModifier;
      this.questions = questions;
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
}
