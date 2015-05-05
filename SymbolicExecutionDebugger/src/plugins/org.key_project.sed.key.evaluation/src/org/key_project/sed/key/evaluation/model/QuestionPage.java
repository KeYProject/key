package org.key_project.sed.key.evaluation.model;

import java.util.List;

import org.key_project.util.java.CollectionUtil;

public class QuestionPage extends AbstractPage {
   private final List<AbstractQuestion> questions;

   public QuestionPage(String name, String title, String message, AbstractQuestion... questions) {
      this(name, title, message, CollectionUtil.toList(questions));
   }

   public QuestionPage(String name, String title, String message, List<AbstractQuestion> questions) {
      super(name, title, message);
      this.questions = questions;
   }

   public AbstractQuestion[] getQuestions() {
      return questions.toArray(new AbstractQuestion[questions.size()]);
   }

   public int countQuestions() {
      return questions.size();
   }
}
