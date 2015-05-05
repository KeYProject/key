package org.key_project.sed.key.evaluation.model_input;

import org.key_project.sed.key.evaluation.model.SendFormPage;

public class SendFormPageInput extends AbstractPageInput<SendFormPage> {
   private final QuestionInput acceptInput;
   
   public SendFormPageInput(SendFormPage page) {
      super(page);
      acceptInput = new QuestionInput(page.getAcceptQuestion());
   }

   public QuestionInput getAcceptInput() {
      return acceptInput;
   }

   @Override
   public void appendXMLContent(int level, StringBuffer sb) {
      // Nothing to do
   }
}
