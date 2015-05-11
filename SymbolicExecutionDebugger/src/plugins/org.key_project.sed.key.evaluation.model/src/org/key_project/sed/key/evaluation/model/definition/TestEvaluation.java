package org.key_project.sed.key.evaluation.model.definition;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.List;

import org.key_project.sed.key.evaluation.model.validation.FixedValueValidator;
import org.key_project.util.java.CollectionUtil;

public class TestEvaluation extends AbstractEvaluation {
   /**
    * The only instance of this class.
    */
   public static TestEvaluation INSTANCE = new TestEvaluation();
   
   private TestEvaluation() {
      super("Test Evaluation");
   }

   @Override
   protected List<AbstractForm> computeForms() {
      try {         
         QuestionPage questionPage = new QuestionPage("questionPage", 
                                                      "questionPageTitle", 
                                                      "questionPageMessage",
                                                      null,
                                                      new BrowserQuestion("browserQuestion", new URL("http://key-project.org/")),
                                                      new RadioButtonsQuestion("radioQuestions", "radioQuestionsLabel", "no", new FixedValueValidator("yes", "errorMessage"), new RadioButtonsQuestion.Choice("Yes", "yes"), new RadioButtonsQuestion.Choice("No", "no")));
         SendFormPage sendFixedPage = new SendFormPage("sendFixedPage", "sendFixedPageTitle", "sendFixedPageMessage", "additionalDataCollectedByServer");
         FixedForm fixedForm = new FixedForm("fixedForm", questionPage, sendFixedPage);
         QuestionPage random1Page = new QuestionPage("random1Page", "random1PageTitle", "random1PageMessage", null);
         QuestionPage random2Page = new QuestionPage("random2Page", "random2PageTitle", "random2PageMessage", null);
         QuestionPage random3Page = new QuestionPage("random3Page", "random3PageTitle", "random3PageMessage", null);
         SendFormPage sendRandomPage = new SendFormPage("sendRandomPage", "sendRandomPageTitle", "sendRandomPageMessage", "additionalDataCollectedByServer");
         RandomForm randomForm = new RandomForm("randomForm", random1Page, random2Page, random3Page, sendRandomPage);
         return CollectionUtil.toList(fixedForm, randomForm);
      }
      catch (MalformedURLException e) {
         throw new IllegalArgumentException(e);
      }
   }

   @Override
   protected List<Tool> computeTools() {
      Tool t1 = new Tool("tool1");
      Tool t2 = new Tool("tool2");
      return CollectionUtil.toList(t1, t2);
   }
}
