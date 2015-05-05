package org.key_project.sed.key.evaluation.model_input;

import java.util.ArrayList;
import java.util.List;

import org.key_project.sed.key.evaluation.model.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.QuestionPage;

public class QuestionPageInput extends AbstractPageInput<QuestionPage> {
   private final List<QuestionInput> questionInputs;

   public QuestionPageInput(QuestionPage page) {
      super(page);
      this.questionInputs = new ArrayList<QuestionInput>(page.countQuestions());
      for (AbstractQuestion question : page.getQuestions()) {
         this.questionInputs.add(new QuestionInput(question));
      }
   }

   public QuestionInput[] getQuestionInputs() {
      return questionInputs.toArray(new QuestionInput[questionInputs.size()]);
   }
   
   @Override
   protected void appendPageContent(int level, StringBuffer sb) {
      for (QuestionInput questionInput : questionInputs) {
         questionInput.appendXMLContent(level, sb);
      }
   }
}
