package org.key_project.sed.key.evaluation.model.input;

import org.key_project.sed.key.evaluation.model.definition.SendFormPage;

public class SendFormPageInput extends AbstractPageInput<SendFormPage> {
   public static final String PROP_SENDING_IN_PROGRESS = "sendingInProgress";

   private final QuestionInput acceptInput;
   
   private boolean sendingInProgress = false;
   
   public SendFormPageInput(AbstractFormInput<?> formInput, SendFormPage page) {
      super(formInput, page);
      acceptInput = new QuestionInput(this, page.getAcceptQuestion());
   }

   public QuestionInput getAcceptInput() {
      return acceptInput;
   }

   public boolean isSendingInProgress() {
      return sendingInProgress;
   }

   public void setSendingInProgress(boolean sendingInProgress) {
      boolean oldValue = isSendingInProgress();
      this.sendingInProgress = sendingInProgress;
      firePropertyChange(PROP_SENDING_IN_PROGRESS, oldValue, isSendingInProgress());
   }

   @Override
   public void reset() {
      acceptInput.reset();
      setSendingInProgress(false);
      super.reset();
   }
}
