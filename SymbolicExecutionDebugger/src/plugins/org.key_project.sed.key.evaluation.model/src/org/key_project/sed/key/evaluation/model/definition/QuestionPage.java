package org.key_project.sed.key.evaluation.model.definition;

import java.util.List;

import org.key_project.sed.key.evaluation.model.tooling.IWorkbenchModifier;
import org.key_project.util.java.CollectionUtil;

public class QuestionPage extends AbstractPage {
   private final List<AbstractQuestion> questions;

   private final IWorkbenchModifier workbenchModifier;
   
   public QuestionPage(String name, String title, String message, IWorkbenchModifier workbenchModifier, AbstractQuestion... questions) {
      this(name, title, message, workbenchModifier, CollectionUtil.toList(questions));
   }

   public QuestionPage(String name, String title, String message, IWorkbenchModifier workbenchModifier, List<AbstractQuestion> questions) {
      super(name, title, message);
      this.workbenchModifier = workbenchModifier;
      this.questions = questions;
   }

   public AbstractQuestion[] getQuestions() {
      return questions.toArray(new AbstractQuestion[questions.size()]);
   }

   public int countQuestions() {
      return questions.size();
   }

   public IWorkbenchModifier getWorkbenchModifier() {
      return workbenchModifier;
   }
}
