package org.key_project.sed.key.evaluation.model.definition;

import org.key_project.sed.key.evaluation.model.validation.FixedValueValidator;

public class SendFormPage extends AbstractPage {
   private final String additionalDataCollectedByServer;
   
   private final RadioButtonsQuestion acceptQuestion = new RadioButtonsQuestion("acceptSending", 
                                                                                null, 
                                                                                false,
                                                                                "no", 
                                                                                new FixedValueValidator("yes", "Conditions of sending are not accepted."),
                                                                                false,
                                                                                new Choice("I &accept that the content will be sent and that the additional data will be stored.", "yes"),
                                                                                new Choice("I do n&ot accept", "no"));

   public SendFormPage(String name, String title, String message, String additionalDataCollectedByServer) {
      super(name, title, message, false, false, true);
      this.additionalDataCollectedByServer = additionalDataCollectedByServer;
   }
   
   public boolean isReadonly() {
      return true;
   }

   public String getAdditionalDataCollectedByServer() {
      return additionalDataCollectedByServer;
   }

   public RadioButtonsQuestion getAcceptQuestion() {
      return acceptQuestion;
   }
}
