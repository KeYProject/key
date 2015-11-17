package org.key_project.sed.key.evaluation.model.input;

import java.util.ArrayList;
import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

public class QuestionPageInput extends AbstractPageInput<QuestionPage> {
   private final List<QuestionInput> questionInputs;

   public QuestionPageInput(AbstractFormInput<?> formInput, QuestionPage page) {
      super(formInput, page);
      this.questionInputs = new ArrayList<QuestionInput>(page.countQuestions());
      for (AbstractQuestion question : page.getQuestions()) {
         this.questionInputs.add(new QuestionInput(this, question));
      }
   }

   public QuestionInput[] getQuestionInputs() {
      return questionInputs.toArray(new QuestionInput[questionInputs.size()]);
   }

   public QuestionInput getQuestionInput(final String questionName) {
      return CollectionUtil.search(questionInputs, new IFilter<QuestionInput>() {
         @Override
         public boolean select(QuestionInput element) {
            return ObjectUtil.equals(questionName, element.getQuestion().getName());
         }
      });
   }

   @Override
   public void reset() {
      for (QuestionInput questionInput : questionInputs) {
         questionInput.reset();
      }
      super.reset();
   }
}
