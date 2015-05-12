package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;
import java.util.List;

import org.key_project.sed.key.evaluation.model.Activator;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion.Choice;
import org.key_project.sed.key.evaluation.model.random.UnderstandingProofAttemptsRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.model.tooling.JavaProjectModifier;
import org.key_project.sed.key.evaluation.model.tooling.JavaProjectModifier.FileDefinition;
import org.key_project.sed.key.evaluation.model.tooling.ProofAttemptJavaProjectModifier;
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
    * Page name of proof 1.
    */
   public static final String PROOF_1_PAGE_NAME = "proof1";

   /**
    * Page name of proof 2.
    */
   public static final String PROOF_2_PAGE_NAME = "proof2";

   /**
    * Page name of proof 3.
    */
   public static final String PROOF_3_PAGE_NAME = "proof3";

   /**
    * Page name of proof 4.
    */
   public static final String PROOF_4_PAGE_NAME = "proof4";

   /**
    * Page name of the send evaluation page.
    */
   public static final String SEND_EVALUATION_PAGE_NAME = "sendEvaluation";

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
      URL keyURL = Activator.getDefault().getBundle().getEntry("data/understandingProofAttempts/KeY.html");
      URL sedURL = Activator.getDefault().getBundle().getEntry("data/understandingProofAttempts/SED.html");
      Tool key = new Tool(KEY_TOOL_NAME, keyURL);
      Tool sed = new Tool(SED_TOOL_NAME, sedURL);
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
                                                     null,
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
                                                     null,
                                                     new RadioButtonsQuestion("experienceWithJava",
                                                                              "Experience with Java: ", 
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with Java not defined."), 
                                                                              new Choice("None", "None"), 
                                                                              new Choice("< 2 years", "Less than 2 years"), 
                                                                              new Choice(">= 2 years", "More than 2 years")),
                                                     new RadioButtonsQuestion("experienceWithKeY",
                                                                              "Experience with KeY: ", 
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with KeY not defined."), 
                                                                              new Choice("None", "None"), 
                                                                              new Choice("< 2 years", "Less than 2 years"), 
                                                                              new Choice(">= 2 years", "More than 2 years")),
                                                     new RadioButtonsQuestion("experienceWithSED",
                                                                              "Experience with SED: ", 
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with SED not defined."), 
                                                                              new Choice("None", "None"), 
                                                                              new Choice("< 1 year", "Less than 1 year"), 
                                                                              new Choice(">= 1 year", "More than 1 year")));
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
      ToolPage keyToolPage = new ToolPage(getTool(KEY_TOOL_NAME));
      ToolPage sedToolPage = new ToolPage(getTool(SED_TOOL_NAME));
      QuestionPage proof1Page = new QuestionPage(PROOF_1_PAGE_NAME, "Proof Attempt 1", "Please answer the question to the best of your knowledge.", null);
      QuestionPage proof2Page = new QuestionPage(PROOF_2_PAGE_NAME, 
                                                 "Proof Attempt 2", 
                                                 "Please answer the question to the best of your knowledge.", 
                                                 new ProofAttemptJavaProjectModifier("MyInteger",
                                                                                     "add",
                                                                                     new String[] {"QMyInteger;"},
                                                                                     new FileDefinition("data/understandingProofAttempts/proof2/MyInteger.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MyInteger.proof", false),
                                                                                     new FileDefinition("data/understandingProofAttempts/proof2/MyInteger.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MyInteger.java", true)));
      QuestionPage proof3Page = new QuestionPage(PROOF_3_PAGE_NAME, "Proof Attempt 3", "Please answer the question to the best of your knowledge.", null);
      QuestionPage proof4Page = new QuestionPage(PROOF_4_PAGE_NAME, 
                                                 "Proof Attempt 4", 
                                                 "Please answer the question to the best of your knowledge.", 
                                                 new ProofAttemptJavaProjectModifier("MyInteger",
                                                                                     "add",
                                                                                     new String[] {"QMyInteger;"},
                                                                                     new FileDefinition("data/understandingProofAttempts/proof2/MyInteger.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MyInteger.proof", false),
                                                                                     new FileDefinition("data/understandingProofAttempts/proof2/MyInteger.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MyInteger.java", true)));
      SendFormPage sendEvaluationPage = new SendFormPage(SEND_EVALUATION_PAGE_NAME, 
                                                         "Confirm Sending Content", 
                                                         "Inspect the content to be send.", 
                                                         "Current date and time (nothing else!)");
      RandomForm evaluationForm = new RandomForm("evaluationForm", keyToolPage, sedToolPage, proof1Page, proof2Page, proof3Page, proof4Page, sendEvaluationPage);
      // Create thanks form
      QuestionPage thanksPage = new QuestionPage("thanksPage", "Evaluation sucessfully completed", "Thank you for participating in the evaluation.", null);
      FixedForm thanksForm = new FixedForm("thanksForm", thanksPage);
      // Create forms
      return CollectionUtil.toList(introductionForm, evaluationForm, thanksForm);
   }
   
   public RandomForm getEvaluationForm() {
      return (RandomForm) getForm("evaluationForm");
   }
}
