package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;
import java.util.List;

import org.key_project.sed.key.evaluation.model.Activator;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion.Choice;
import org.key_project.sed.key.evaluation.model.random.UnderstandingProofAttemptsRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.model.validation.FixedValueValidator;
import org.key_project.sed.key.evaluation.model.validation.NotUndefinedValueValidator;
import org.key_project.util.java.CollectionUtil;

public class UnderstandingProofAttemptsEvaluation extends AbstractEvaluation {
   /**
    * The only instance of this class.
    */
   public static UnderstandingProofAttemptsEvaluation INSTANCE = new UnderstandingProofAttemptsEvaluation();
   
   /**
    * The name of the {@link Tool} representing 'KeY'.
    */
   public static final String KEY_TOOL_NAME = "KeY";

   /**
    * The name of the {@link Tool} representing 'SED'.
    */
   public static final String SED_TOOL_NAME = "SED";

   /**
    * Forbid additional instances.
    */
   private UnderstandingProofAttemptsEvaluation() {
      super("Understanding Proof Attempts");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected List<Tool> computeTools() {
      Tool key = new Tool(KEY_TOOL_NAME);
      Tool sed = new Tool(SED_TOOL_NAME);
      return CollectionUtil.toList(key, sed);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected List<AbstractForm> computeForms() {
      // Create introduction form
      URL conditionsURL = Activator.getDefault().getBundle().getEntry("data/understandingProofAttempts/conditions.html");
      QuestionPage conditionsPage = new QuestionPage("conditionsPage", 
                                                     "Introduction", 
                                                     "Please read the information and conditions of the evaluation carefully.",
                                                     new BrowserQuestion("conditions", conditionsURL),
                                                     new RadioButtonsQuestion("acceptConditions",
                                                                              null, 
                                                                              "no", 
                                                                              new FixedValueValidator("yes", "Conditions are not accepted."), 
                                                                              new Choice("I &accept the conditions", "yes"), 
                                                                              new Choice("I do &not accept the conditions", "no")));
      QuestionPage backgroundPage = new QuestionPage("backgroundPage", 
                                                     "Background", 
                                                     "Please fill out the form with your background knowledge.",
                                                     new RadioButtonsQuestion("experienceWithJava",
                                                                              "Experience with Java: ", 
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with Java not defined."), 
                                                                              new Choice("None", "none"), 
                                                                              new Choice("< 1 year", "beginner"), 
                                                                              new Choice(">= 1 year", "experiencedUser")),
                                                     new RadioButtonsQuestion("experienceWithKeY",
                                                                              "Experience with KeY: ", 
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with KeY not defined."), 
                                                                              new Choice("None", "none"), 
                                                                              new Choice("< 1 year", "beginner"), 
                                                                              new Choice(">= 1 year", "experiencedUser")),
                                                     new RadioButtonsQuestion("experienceWithSED",
                                                                              "Experience with SED: ", 
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with SED not defined."), 
                                                                              new Choice("None", "none"), 
                                                                              new Choice("< 1 year", "beginner"), 
                                                                              new Choice(">= 1 year", "experiencedUser")));
      SendFormPage sendConditionsPage = new SendFormPage("sendConditions", 
                                                         "Confirm Sending Content", 
                                                         "Inspect the content to be send.", 
                                                         "Current date and time (nothing else!)");
      FixedForm introductionForm = new FixedForm("introductionForm", 
                                                 new UnderstandingProofAttemptsRandomFormOrderComputer(),
                                                 conditionsPage, 
                                                 backgroundPage,
                                                 sendConditionsPage);
      // Create evaluation form
      QuestionPage proof1Page = new QuestionPage("proof1", "Proof Attempt 1", "Please answer the question to the best of your knowledge.");
      QuestionPage proof2Page = new QuestionPage("proof2", "Proof Attempt 2", "Please answer the question to the best of your knowledge.");
      QuestionPage proof3Page = new QuestionPage("proof3", "Proof Attempt 3", "Please answer the question to the best of your knowledge.");
      QuestionPage proof4Page = new QuestionPage("proof4", "Proof Attempt 4", "Please answer the question to the best of your knowledge.");
      SendFormPage sendEvaluationPage = new SendFormPage("sendEvaluation", 
                                                         "Confirm Sending Content", 
                                                         "Inspect the content to be send.", 
                                                         "Current date and time (nothing else!)");
      RandomForm evaluationForm = new RandomForm("evaluationForm", proof1Page, proof2Page, proof3Page, proof4Page, sendEvaluationPage);
      // Create thanks form
      QuestionPage thanksPage = new QuestionPage("thanksPage", "Evaluation sucessfully completed", "Thank you for participating in the evaluation.");
      FixedForm thanksForm = new FixedForm("thanksForm", thanksPage);
      // Create forms
      return CollectionUtil.toList(introductionForm, evaluationForm, thanksForm);
   }
   
   public RandomForm getEvaluationForm() {
      return (RandomForm) getForm("evaluationForm");
   }
}
