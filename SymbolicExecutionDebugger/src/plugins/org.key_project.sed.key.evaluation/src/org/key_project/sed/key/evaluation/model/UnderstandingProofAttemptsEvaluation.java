package org.key_project.sed.key.evaluation.model;

import java.net.URL;
import java.util.LinkedList;
import java.util.List;

import org.key_project.sed.key.evaluation.Activator;
import org.key_project.sed.key.evaluation.model.RadioButtonsQuestion.Choice;
import org.key_project.sed.key.evaluation.model.validation.FixedValueValidator;
import org.key_project.sed.key.evaluation.model.validation.NotUndefinedValueValidator;
import org.key_project.sed.key.evaluation.model_input.EvaluationInput;

public class UnderstandingProofAttemptsEvaluation extends AbstractEvaluation {
   /**
    * The only instance of this class.
    */
   public static UnderstandingProofAttemptsEvaluation INSTANCE = new UnderstandingProofAttemptsEvaluation();
   
   /**
    * The {@link EvaluationInput} to perform {@link #INSTANCE}.
    */
   public static EvaluationInput INPUT_INSTANCE = new EvaluationInput(INSTANCE);
   
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
   protected List<Form> computeForms() {
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
      Form introductionForm = new Form("introductionForm", 
                                       conditionsPage, 
                                       backgroundPage,
                                       sendConditionsPage);
      sendConditionsPage.setForm(introductionForm);
      // Create forms
      List<Form> forms = new LinkedList<Form>();
      forms.add(introductionForm);
      return forms;
   }
}
