package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;
import java.util.List;

import org.key_project.sed.key.evaluation.model.tooling.JavaProjectModifier;
import org.key_project.sed.key.evaluation.model.tooling.JavaProjectModifier.FileDefinition;
import org.key_project.sed.key.evaluation.model.tooling.ProofAttemptJavaProjectModifier;
import org.key_project.sed.key.evaluation.model.util.EvaluationModelImages;
import org.key_project.sed.key.evaluation.model.validation.FixedValueValidator;
import org.key_project.sed.key.evaluation.model.validation.NotUndefinedValueValidator;
import org.key_project.util.java.CollectionUtil;

public class UnderstandingProofAttemptsEvaluation extends AbstractEvaluation {
   /**
    * The only instance of this class.
    */
   public static final UnderstandingProofAttemptsEvaluation INSTANCE = new UnderstandingProofAttemptsEvaluation();
   
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
    * Page name of the JML introduction page.
    */
   public static final String JML_PAGE_NAME = "JML";

   /**
    * Page name of the summary page.
    */
   public static final String FEEDBACK_PAGE = "summary";

   /**
    * Page name of the evaluation instruction page.
    */
   public static final String EVALUATION_PAGE_NAME = "evaluationInstructions";

   /**
    * The name of the used random order computer.
    */
   public static final String RANDOM_COMPUTER_NAME = "UnderstandingProofAttemptsRandomFormOrderComputer";

   /**
    * The name of the evaluation form.
    */
   public static final String EVALUATION_FORM_NAME = "evaluationForm";

   /**
    * The name of the introduction form.
    */
   public static final String INTRODUCTION_FORM_NAME = "introductionForm";

   /**
    * The name of the page with the background knowledge.
    */
   public static final String BACKGROUND_PAGE_NAME = "backgroundPage";

   /**
    * The name of the question defining the background knowledge with KeY.
    */
   public static final String EXPERIENCE_WITH_KEY_QUESTION_NAME = "experienceWithKeY";

   /**
    * The value of no KeY experience.
    */
   public static final String KEY_EXPERIENCE_NON_VALUE = "None";

   /**
    * The value for less than 2 years of KeY experience.
    */
   public static final String KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE = "Less than 2 years";

   /**
    * The value for more than 2 years of KeY experience.
    */
   public static final String KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE = "More than 2 years";

   /**
    * Forbid additional instances.
    */
   private UnderstandingProofAttemptsEvaluation() {
      super("Understanding Proof Attempts", isUIAvailable() ? "data/understandingProofAttempts/instructions/" : null);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected List<Tool> computeTools() {
      URL keyURL = isUIAvailable() ? toLocalURL("data/understandingProofAttempts/instructions/KeY-Screencast.html") : null;
      URL keyWizardURL = isUIAvailable() ? toLocalURL("data/understandingProofAttempts/instructions/KeY-ScreencastWizard.html") : null;
      URL sedURL = isUIAvailable() ? toLocalURL("data/understandingProofAttempts/instructions/SED-Screencast.html") : null;
      URL sedWizardURL = isUIAvailable() ? toLocalURL("data/understandingProofAttempts/instructions/SED-ScreencastWizard.html") : null;
      Tool key = new Tool(KEY_TOOL_NAME, 
                          keyURL, 
                          keyWizardURL,
                          isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_LOGO) : null);
      Tool sed = new Tool(SED_TOOL_NAME, 
                          sedURL, 
                          sedWizardURL,
                          isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_LOGO) : null);
      return CollectionUtil.toList(key, sed);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected List<AbstractForm> computeForms() {
      // Create introduction form
      URL conditionsURL = isUIAvailable() ? toLocalURL("data/understandingProofAttempts/instructions/conditions.html") : null;
      QuestionPage conditionsPage = new QuestionPage("conditionsPage", 
                                                     "Introduction", 
                                                     "Please read the information and conditions of the evaluation carefully.",
                                                     false,
                                                     false,
                                                     null,
                                                     new BrowserQuestion("conditions", conditionsURL),
                                                     new RadioButtonsQuestion("acceptConditions",
                                                                              null, 
                                                                              true,
                                                                              "no", 
                                                                              new FixedValueValidator("yes", "Please read and accept the information and conditions of the evaluation."), 
                                                                              false,
                                                                              new Choice("I &accept the conditions", "yes"), 
                                                                              new Choice("I do &not accept the conditions", "no")));
      QuestionPage backgroundPage = new QuestionPage(BACKGROUND_PAGE_NAME, 
                                                     "Background Knowledge", 
                                                     "Please fill out the form with your background knowledge.",
                                                     true,
                                                     false,
                                                     null,
                                                     new RadioButtonsQuestion("experienceWithJava",
                                                                              "Experience with Java", 
                                                                              true,
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with Java not defined."), 
                                                                              false,
                                                                              new Choice("None", "None"), 
                                                                              new Choice("< 2 years", "Less than 2 years"), 
                                                                              new Choice(">= 2 years", "More than 2 years")),
                                                     new RadioButtonsQuestion("experienceWithJML",
                                                                              "Experience with JML", 
                                                                              true,
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with JML not defined."), 
                                                                              false,
                                                                              new Choice("None", "None"), 
                                                                              new Choice("< 2 years", "Less than 2 years"), 
                                                                              new Choice(">= 2 years", "More than 2 years")),
                                                     new RadioButtonsQuestion(EXPERIENCE_WITH_KEY_QUESTION_NAME,
                                                                              "Experience with KeY", 
                                                                              true,
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with KeY not defined."), 
                                                                              false,
                                                                              new Choice("None", KEY_EXPERIENCE_NON_VALUE), 
                                                                              new Choice("< 2 years", KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE), 
                                                                              new Choice(">= 2 years", KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE)),
                                                     new RadioButtonsQuestion("experienceWithSED",
                                                                              "Experience with SED", 
                                                                              true,
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with SED not defined."), 
                                                                              false,
                                                                              new Choice("None", "None"), 
                                                                              new Choice("< 1 year", "Less than 1 year"), 
                                                                              new Choice(">= 1 year", "More than 1 year")));
      SendFormPage sendConditionsPage = new SendFormPage("sendConditions", 
                                                         "Confirm Sending Background Knowledge (used to order proof attempts)", 
                                                         "Optionally, inspect the answers to be sent.", 
                                                         "Current date and time (nothing else!)");
      FixedForm introductionForm = new FixedForm(INTRODUCTION_FORM_NAME, 
                                                 false,
                                                 RANDOM_COMPUTER_NAME,
                                                 conditionsPage, 
                                                 backgroundPage,
                                                 sendConditionsPage);
      // Create evaluation form
      URL evaluationURL = isUIAvailable() ? toLocalURL("data/understandingProofAttempts/instructions/EvaluationIntroduction-Screencast.html") : null;
      URL jmlURL = isUIAvailable() ? toLocalURL("data/understandingProofAttempts/instructions/JML.html") : null;
      InstructionPage evaluationPage = new InstructionPage(EVALUATION_PAGE_NAME, "Evaluation Instructions", "Read the evaluation instructions carefully before continuing.", evaluationURL, isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.EVALUATION) : null);
      InstructionPage jmlPage = new InstructionPage(JML_PAGE_NAME, "JML", "Read the JML introduction carefully before continuing.", jmlURL, isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.JML_LOGO) : null);
      ToolPage keyToolPage = new ToolPage(getTool(KEY_TOOL_NAME),
                                          new ProofAttemptJavaProjectModifier("Example",
                                                                              "magic",
                                                                              new String[] {"I", "QExample;", "QExample;"},
                                                                              "magic(int, Example, Example)",
                                                                              false,
                                                                              new FileDefinition("data/understandingProofAttempts/instructions-archived/instructionProof/ExampleKeY.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Example.proof", false),
                                                                              new FileDefinition("data/understandingProofAttempts/instructions-archived/instructionProof/Example.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Example.java", true)),
                                          false);
            
      ToolPage sedToolPage = new ToolPage(getTool(SED_TOOL_NAME),
                                          new ProofAttemptJavaProjectModifier("Example",
                                                                              "magic",
                                                                              new String[] {"I", "QExample;", "QExample;"},
                                                                              "magic(int, Example, Example)",
                                                                              false,
                                                                              new FileDefinition("data/understandingProofAttempts/instructions-archived/instructionProof/ExampleSED.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Example.proof", false),
                                                                              new FileDefinition("data/understandingProofAttempts/instructions-archived/instructionProof/Example.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Example.java", true)),
                                          false);
      QuestionPage proof1Page = createCalendarQuestionPage(PROOF_1_PAGE_NAME, "Proof Attempt of Calendar#addEntry(Entry)");
      QuestionPage proof2Page = createAccountQuestionPage(PROOF_2_PAGE_NAME, "Proof Attempt of Account#checkAndWithdraw(int)");
      QuestionPage proof3Page = createMinQuestionPage(PROOF_3_PAGE_NAME, "Proof Attempt of ArrayUtil#minIndex(int[])");
      QuestionPage proof4Page = createMyIntegerQuestionPage(PROOF_4_PAGE_NAME, "Proof Attempt of MyInteger#add(MyInteger)");
      QuestionPage feedbackPage = createFeedbackPage();
      SendFormPage sendEvaluationPage = new SendFormPage(SEND_EVALUATION_PAGE_NAME, 
                                                         "Confirm Sending Evaluation Answers", 
                                                         "Optionally, inspect the answers to be sent.", 
                                                         "Current date and time (nothing else!)");
      RandomForm evaluationForm = new RandomForm(EVALUATION_FORM_NAME, true, evaluationPage, jmlPage, keyToolPage, sedToolPage, proof1Page, proof2Page, proof3Page, proof4Page, feedbackPage, sendEvaluationPage);
      // Create thanks form
      QuestionPage thanksPage = new QuestionPage("thanksPage", 
                                                 "Evaluation sucessfully completed", 
                                                 "Thank you for participating in the evaluation.", 
                                                 false, 
                                                 false,
                                                 null,
                                                 new ImageQuestion("thanksImage", isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_THANKS, 25) : null));
      FixedForm thanksForm = new FixedForm("thanksForm", false, thanksPage);
      // Create forms
      return CollectionUtil.toList(introductionForm, evaluationForm, thanksForm);
   }
   
   public RandomForm getEvaluationForm() {
      return (RandomForm) getForm(EVALUATION_FORM_NAME);
   }

   private QuestionPage createMyIntegerQuestionPage(String pageName, String title) {
      String locationTitle = "Which not specified location(s) have changed?";
      CheckboxQuestion locationQuestion = new CheckboxQuestion("whichLocationsHaveChanged", 
                                                               locationTitle, 
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + locationTitle + "' not answered."), 
                                                               true,
                                                               new Choice("self", "self"),
                                                               new Choice("self.value", "self.value"),
                                                               new Choice("summand", "summand"),
                                                               new Choice("summand.value", "summand.value"),
                                                               new Choice("something else", "something else", createElseLocationSubQuestion()),
                                                               new Choice("none", "none"),
                                                               createGiveupLocationChoice());
      String whyOpenTitle = "Why is the proof still open?";
      CheckboxQuestion whyOpenQuestion = new CheckboxQuestion("whyOpen", 
                                                              whyOpenTitle, 
                                                              true,
                                                              null, 
                                                              new NotUndefinedValueValidator("Question '" + whyOpenTitle + "' not answered."), 
                                                              true,
                                                              new Choice(createPreconditionText("summand != null"), createPreconditionValue()),
                                                              new Choice(createPostconditionText("value == \\old(value) + summand.value"), createPostconditionValue(), true),
                                                              new Choice(createMethodAssignableText(), createMethodAssignableValue(), locationQuestion),
                                                              new Choice(createExceptionThrownText(), createExceptionThrownValue(), createThrownExceptionsQuestion()),
                                                              createBugfreeChoice(),
                                                              createSomethingElseIsReasonChoice(),
                                                              createGiveupWhyOpenChoice());
      String openQuestionTitle = "Is the method successfully verified (Is the proof closed)?";
      RadioButtonsQuestion openQuestion = new RadioButtonsQuestion("openOrClosed", 
                                                                   openQuestionTitle, 
                                                                   true,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + openQuestionTitle + "' not answered."), 
                                                                   true,
                                                                   new Choice("Yes", "Yes"), 
                                                                   new Choice("No", "No", true, whyOpenQuestion));
      String executedTitle = "Was statement (value += summand.value) at line 9 executed during symbolic execution of the proof?";
      RadioButtonsQuestion executedQuestion = new RadioButtonsQuestion("executedStatements", 
                                                                       executedTitle, 
                                                                       true,
                                                                       null, 
                                                                       new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                                       true,
                                                                       new Choice("Yes", "Yes", true),
                                                                       new Choice("No", "No"));
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              new ProofAttemptJavaProjectModifier("MyInteger",
                                                                  "add",
                                                                  new String[] {"QMyInteger;"},
                                                                  "add(MyInteger)",
                                                                  true,
                                                                  new FileDefinition("data/understandingProofAttempts/proofMyInteger/MyInteger.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MyInteger.proof", false),
                                                                  new FileDefinition("data/understandingProofAttempts/proofMyInteger/MyInteger.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MyInteger.java", true)),
                              new LabelQuestion("generalDescription", createGeneralDescription("MyInteger#add(MyInteger)")),
                              openQuestion,
                              executedQuestion);
   }

   private QuestionPage createMinQuestionPage(String pageName, String title) {
      String whyOpenTitle = "Why is the proof still open?";
      CheckboxQuestion whyOpenQuestion = new CheckboxQuestion("whyOpen", 
                                                              whyOpenTitle, 
                                                              true,
                                                              null, 
                                                              new NotUndefinedValueValidator("Question '" + whyOpenTitle + "' not answered."), 
                                                              true,
                                                              new Choice(createPreconditionText("array != null"), createPreconditionValue(), createMinTerminationQuestion("preconditionTermination", false, false)),
                                                              new Choice(createPostconditionText("array == null || array.length == 0 ==> \\result == -1"), createPostconditionValue("Not found"), createMinTerminationQuestion("postNotFoundTermination", false, false)),
                                                              new Choice(createPostconditionText("array != null && array.length >= 1 ==> (\\forall int i; i >= 0 && i < array.length; array[\\result] <= array[i])"), createPostconditionValue("Found"), true, createMinTerminationQuestion("postFoundTermination", true, false)),
                                                              new Choice(createMethodAssignableText(), createMethodAssignableValue(), createMinLocationQuestion("whichMethodLocationsHaveChanged"), createMinTerminationQuestion("methodAssignableTermination", false, false)),
                                                              new Choice(createExceptionThrownText(), createExceptionThrownValue(), createThrownExceptionsQuestion()),
                                                              new Choice(createLoopInvariantInitiallyText("i >= 1 && i <= array.length"), createLoopInvariantInitiallyValue("i"), createMinTerminationQuestion("initialITermination", false, false)),
                                                              new Choice(createLoopInvariantInitiallyText("minIndex >= 0 && minIndex < i"), createLoopInvariantInitiallyValue("minIndex"), createMinTerminationQuestion("initialMinIndexTermination", false, false)),
                                                              new Choice(createLoopInvariantInitiallyText("\\forall int j; j >= 0 && j < i; array[minIndex] <= array[j]"), createLoopInvariantInitiallyValue("array elements"), createMinTerminationQuestion("initialArrayElementsTermination", false, false)),
                                                              new Choice(createLoopInvariantPreservedText("i >= 1 && i <= array.length"), createLoopInvariantPreservedValue("i"), createMinTerminationQuestion("preservedITermination", false, false)),
                                                              new Choice(createLoopInvariantPreservedText("minIndex >= 0 && minIndex < i"), createLoopInvariantPreservedValue("minIndex"), createMinTerminationQuestion("preservedMinIndexTermination", false, false)),
                                                              new Choice(createLoopInvariantPreservedText("\\forall int j; j >= 0 && j < i; array[minIndex] <= array[j]"), createLoopInvariantPreservedValue("array elements"), true, createMinTerminationQuestion("preservedArrayElementsTermination", false, true)),
                                                              new Choice(createDecreasingText("array.length - i"), createDecreasingValue(), createMinTerminationQuestion("decreasingTermination", false, false)),
                                                              new Choice(createLoopAssignableText(), createLoopAssignableValue(), createMinLocationQuestion("whichLoopLocationsHaveChanged"), createMinTerminationQuestion("loopAssignableTermination", false, false)),
                                                              createBugfreeChoice(),
                                                              createSomethingElseIsReasonChoice(),
                                                              createGiveupWhyOpenChoice());
      String openQuestionTitle = "Is the method successfully verified (Is the proof closed)?";
      RadioButtonsQuestion openQuestion = new RadioButtonsQuestion("openOrClosed", 
                                                                   openQuestionTitle, 
                                                                   true,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + openQuestionTitle + "' not answered."), 
                                                                   true,
                                                                   new Choice("Yes", "Yes"), 
                                                                   new Choice("No", "No", true, whyOpenQuestion));
      String executedTitle = "Which statement(s) are executed at least once during symbolic execution of the proof?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements was executed", "None"),
                                                               new Choice("Line 8: if (array != null)", "Line 8", true),
                                                               new Choice("Line 9: if (array.length == 0)", "Line 9", true),
                                                               new Choice("Line 10: return -1", "Line 10", true),
                                                               new Choice("Line 13: array.length == 1", "Line 13", true),
                                                               new Choice("Line 14: return array[0]", "Line 14", true),
                                                               new Choice("Line 17: int minIndex = 0", "Line 17", true),
                                                               new Choice("Line 25: int i = 1", "Line 25 initial", true),
                                                               new Choice("Line 25: i < array.length", "Line 25 condition", true),
                                                               new Choice("Line 25: i++", "Line 25 update", true),
                                                               new Choice("Line 26: if (array[i] < array[minIndex])", "Line 26", true),
                                                               new Choice("Line 27: minIndex = 1", "Line 27", true),
                                                               new Choice("Line 34: return minIndex", "Line 34", true),
                                                               new Choice("Line 39: return -1", "Line 39", true),
                                                               createGiveupExecutedChoice());
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              new ProofAttemptJavaProjectModifier("ArrayUtil",
                                                                  "minIndex",
                                                                  new String[] {"[I"},
                                                                  "minIndex(int[])",
                                                                  true,
                                                                  new FileDefinition("data/understandingProofAttempts/proofMin/ArrayUtil.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ArrayUtil.proof", false),
                                                                  new FileDefinition("data/understandingProofAttempts/proofMin/ArrayUtil.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ArrayUtil.java", true)),
                              new LabelQuestion("generalDescription", createGeneralDescription("ArrayUtil#minIndex(int[])")),
                              openQuestion,
                              executedQuestion);
   }

   private CheckboxQuestion createThrownExceptionsQuestion() {
      String thrownExceptionTitle = "Which exception(s) are thrown?";
      CheckboxQuestion thrownExceptionQuestion = new CheckboxQuestion("whichExceptionsAreThrown", 
                                                                      thrownExceptionTitle, 
                                                                      true,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + thrownExceptionTitle + "' not answered."), 
                                                                      true,
                                                                      new Choice("java.lang.NullPointerException", "java.lang.NullPointerException"),
                                                                      new Choice("java.lang.ArithmeticException", "java.lang.ArithmeticException"),
                                                                      new Choice("java.lang.ArrayIndexOutOfBoundsException", "java.lang.ArrayIndexOutOfBoundsException"),
                                                                      new Choice("java.lang.ArrayStoreException", "java.lang.ArrayStoreException"),
                                                                      new Choice("java.lang.IllegalArgumentException", "java.lang.IllegalArgumentException"),
                                                                      new Choice("java.lang.IllegalStateException", "java.lang.IllegalStateException"),
                                                                      new Choice("java.lang.invoke.WrongMethodTypeException", "java.lang.invoke.WrongMethodTypeException"),
                                                                      new Choice("javax.naming.OperationNotSupportedException", "javax.naming.OperationNotSupportedException"),
                                                                      new Choice("java.lang.OutOfMemoryError", "java.lang.OutOfMemoryError"),
                                                                      new Choice("something else", "something else", createElseExceptionSubQuestion()),
                                                                      new Choice("none", "none"),
                                                                      createGiveupExceptionChoice());
      return thrownExceptionQuestion;
   }

   private CheckboxQuestion createMinLocationQuestion(String name) {
      String title = "Which not specified location(s) have changed?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("array", "array"),
                                  new Choice("array.length", "array.length"),
                                  new Choice("array[0]", "array[0]"),
                                  new Choice("array[*]", "array[*]"),
                                  new Choice("minIndex", "minIndex"),
                                  new Choice("i", "i"),
                                  new Choice("something else", "something else", createElseLocationSubQuestion()),
                                  new Choice("none", "none"),
                                  createGiveupLocationChoice());
   }
   
   private CheckboxQuestion createMinTerminationQuestion(String name, boolean termination2expected, boolean loop1expected) {
      String title = "At which execution path?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("Termination 1: array != null & array.length == 0", "Termination 1"),
                                  new Choice("Termination 2: array != null & array.length == 1", "Termination 2"),
                                  new Choice("Termination 3: array != null & array.length > 1", "Termination 3"),
                                  new Choice("Termination 4: array == null", "Termination 4"),
                                  new Choice("Loop Body Termination 1: array[i] < array[minIndex]", "Loop Body Termination 1", loop1expected),
                                  new Choice("Loop Body Termination 2: array[i] >= array[minIndex]", "Loop Body Termination 2"),
                                  createGiveupTerminationPathChoice());
   }
   
   private QuestionPage createCalendarQuestionPage(String pageName, String title) {
      String whyOpenTitle = "Why is the proof still open?";
      CheckboxQuestion whyOpenQuestion = new CheckboxQuestion("whyOpen", 
                                                              whyOpenTitle, 
                                                              true,
                                                              null, 
                                                              new NotUndefinedValueValidator("Question '" + whyOpenTitle + "' not answered."), 
                                                              true,
                                                              new Choice(createPreconditionText("entry != null"), createPreconditionValue(), createCalendarTerminationQuestion("preconditionTermination", false)),
                                                              new Choice(createClassInvariantInitiallyText("entrySize >= 0 && entrySize < entries.length"), createClassInvariantInitiallyValue(), createCalendarTerminationQuestion("invariantEstablishedTermination", false)),
                                                              new Choice(createPostconditionText("entries[\\old(entrySize)] == entry"), createPostconditionValue("Entry"), createCalendarTerminationQuestion("postEntryTermination", false)),
                                                              new Choice(createPostconditionText("entrySize == \\old(entrySize) + 1"), createPostconditionValue("EntrySize"), createCalendarTerminationQuestion("postEntrySizeTermination", false)),
                                                              new Choice(createClassInvariantPreservedText("entrySize >= 0 && entrySize < entries.length"), createClassInvariantPreservedValue(), true, createCalendarTerminationQuestion("invariantNotPreservedTermination", true)),
                                                              new Choice(createMethodAssignableText(), createMethodAssignableValue(), createCalendarLocationQuestion("whichMethodLocationsHaveChanged"), createCalendarTerminationQuestion("assignableTermination", false)),
                                                              new Choice(createExceptionThrownText(), createExceptionThrownValue(), true, createThrownExceptionsQuestion()),
                                                              new Choice(createLoopInvariantInitiallyText("i >= 0 && i <= entries.length"), createLoopInvariantInitiallyValue("i"), createCalendarTerminationQuestion("loopInvariantIInitialTermination", false)),
                                                              new Choice(createLoopInvariantInitiallyText("\\forall int j; j >= 0 && j < i; newEntries[j] == entries[j]"), createLoopInvariantInitiallyValue("array elements"), createCalendarTerminationQuestion("loopInvariantArrayElementsInitialTermination", false)),
                                                              new Choice(createLoopInvariantPreservedText("i >= 0 && i <= entries.length"), createLoopInvariantPreservedValue("i"), createCalendarTerminationQuestion("loopInvariantIPreservedTermination", false)),
                                                              new Choice(createLoopInvariantPreservedText("\\forall int j; j >= 0 && j < i; newEntries[j] == entries[j]"), createLoopInvariantPreservedValue("array elements"), createCalendarTerminationQuestion("loopInvariantArrayElementsPreservedTermination", false)),
                                                              new Choice(createDecreasingText("entries.length - i"), createDecreasingValue(), createCalendarTerminationQuestion("decreasingTermination", false)),
                                                              new Choice(createLoopAssignableText(), createLoopAssignableValue(), createCalendarLocationQuestion("whichLoopLocationsHaveChanged"), createCalendarTerminationQuestion("loopAssingableTermination", false)),
                                                              createBugfreeChoice(),
                                                              createSomethingElseIsReasonChoice(),
                                                              createGiveupWhyOpenChoice());
      String openQuestionTitle = "Is the method successfully verified (Is the proof closed)?";
      RadioButtonsQuestion openQuestion = new RadioButtonsQuestion("openOrClosed", 
                                                                   openQuestionTitle, 
                                                                   true,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + openQuestionTitle + "' not answered."), 
                                                                   true,
                                                                   new Choice("Yes", "Yes"), 
                                                                   new Choice("No", "No", true, whyOpenQuestion));
      String executedTitle = "Which statement(s) are executed at least once during symbolic execution of the proof?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements was executed", "None"),
                                                               new Choice("Line 14: if (entrySize == entries.length)", "Line 14", true),
                                                               new Choice("Line 15: Entry[] newEntries = new Entry[entries.length * 2]", "Line 15"),
                                                               new Choice("Line 22: int i = 0", "Line 22 initial"),
                                                               new Choice("Line 22: i < entries.length", "Line 22 condition"),
                                                               new Choice("Line 22: i++", "Line 22 update"),
                                                               new Choice("Line 23: newEntries[i] = entries[i]", "Line 23"),
                                                               new Choice("Line 26: entries = newEntries", "Line 26"),
                                                               new Choice("Line 32: entries[entrySize] = entry", "Line 32", true),
                                                               new Choice("Line 33: entrySize++", "Line 33", true),
                                                               createGiveupExecutedChoice());
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              new ProofAttemptJavaProjectModifier("Calendar",
                                                                  "addEntry",
                                                                  new String[] {"QEntry;"},
                                                                  "addEntry(Entry)",
                                                                  true,
                                                                  new FileDefinition("data/understandingProofAttempts/proofCalendar/Calendar.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Calendar.proof", false),
                                                                  new FileDefinition("data/understandingProofAttempts/proofCalendar/Calendar.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Calendar.java", true)),
                              new LabelQuestion("generalDescription", createGeneralDescription("Calendar#addEntry(Entry)")),
                              openQuestion,
                              executedQuestion);
   }

   private CheckboxQuestion createCalendarLocationQuestion(String name) {
      String title = "Which not specified location(s) have changed?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("entries", "entries"),
                                  new Choice("entries[entrySize]", "entries[entrySize]"),
                                  new Choice("entries[*]", "entries[*]"),
                                  new Choice("entries.length", "entries.length"),
                                  new Choice("entrySize", "entrySize"),
                                  new Choice("i", "i"),
                                  new Choice("newEntries", "newEntries"),
                                  new Choice("newEntries.length", "newEntries.length"),
                                  new Choice("newEntries[*]", "newEntries[*]"),
                                  new Choice("something else", "something else", createElseLocationSubQuestion()),
                                  new Choice("none", "none"),
                                  createGiveupLocationChoice());
   }
   
   private CheckboxQuestion createCalendarTerminationQuestion(String name, boolean expectedAfterElse) {
      String title = "At which execution path?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("Continuation After Then: entrySize == entries.length", "Continuation After Then"),
                                  new Choice("Continuation After Else: entrySize != entries.length", "Continuation After Else", expectedAfterElse),
                                  new Choice("Loop Body Termination (of the 'Body Preserves Invariant' branch)", "Loop Body Termination"),
                                  createGiveupTerminationPathChoice());
   }

   private QuestionPage createAccountQuestionPage(String pageName, String title) {
      String whyOpenTitle = "Why is the proof still open?";
      CheckboxQuestion whyOpenQuestion = new CheckboxQuestion("whyOpen", 
                                                              whyOpenTitle, 
                                                              true,
                                                              null, 
                                                              new NotUndefinedValueValidator("Question '" + whyOpenTitle + "' not answered."), 
                                                              true,
                                                              new Choice(createPreconditionText("amount > 0", "checkAndWithdraw(int)"), createPreconditionValue("checkAndWithdraw"), createAccountTerminationQuestion("checkAndWithdrawPreTermination", false)),
                                                              new Choice(createPostconditionText("balance == \\old(balance) - \\result", "checkAndWithdraw(int)"), createPostconditionValue("checkAndWithdraw", "Balance"), createAccountTerminationQuestion("checkAndWithdrawPostconditionBalanceTermination", false)),
                                                              new Choice(createPostconditionText("\\result == amount", "checkAndWithdraw(int)"), createPostconditionValue("checkAndWithdraw", "Result"), true, createAccountTerminationQuestion("checkAndWithdrawPostcondtionResultTermination", true)),
                                                              new Choice(createMethodAssignableText("balance", "checkAndWithdraw(int)"), createMethodAssignableValue("checkAndWithdraw)"), createAccountLocationQuestion("checkAndWithdrawLocations"), createAccountTerminationQuestion("checkAndWithdrawAssignableTermination", false)),
                                                              new Choice(createPreconditionText("amount > 0", "withdraw(int)"), createPreconditionValue("withdraw"), createAccountTerminationQuestion("withdrawPreconditionTermination", false)),
                                                              new Choice(createPreconditionText("amount > 0", "canWithdraw(int)"), createPreconditionValue("canWithdraw"), createAccountTerminationQuestion("canWithdrawPreconditionTermination", false)),
                                                              new Choice(createPreconditionText("true", "getBalance()"), createPreconditionValue("getBalance"), createAccountTerminationQuestion("getBalancePreconditionTermination", false)),
                                                              new Choice(createExceptionThrownText("checkAndWithdraw(int)"), createExceptionThrownValue(), createThrownExceptionsQuestion()),
                                                              createBugfreeChoice(),
                                                              createSomethingElseIsReasonChoice(),
                                                              createGiveupWhyOpenChoice());
      String openQuestionTitle = "Is the method successfully verified (Is the proof closed)?";
      RadioButtonsQuestion openQuestion = new RadioButtonsQuestion("openOrClosed", 
                                                                   openQuestionTitle, 
                                                                   true,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + openQuestionTitle + "' not answered."), 
                                                                   true,
                                                                   new Choice("Yes", "Yes"), 
                                                                   new Choice("No", "No", true, whyOpenQuestion));
      String executedTitle = "Which statement(s) are executed at least once during symbolic execution of the proof?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements was executed", "None"),
                                                               new Choice("Line 11: if (canWithdraw(amount))", "Line 11", true),
                                                               new Choice("Line 12: withdraw(amount)", "Line 12", true),
                                                               new Choice("Line 13: return amount", "Line 13", true),
                                                               new Choice("Line 16: return 0", "Line 16", true),
                                                               new Choice("Line 26: balance -= amount", "Line 26"),
                                                               new Choice("Line 35: return amount > 0", "Line 35"),
                                                               new Choice("Line 44: return balance", "Line 44"),
                                                               createGiveupExecutedChoice());
      String contractsTitle = "Which method contracts are applied at least once during symbolic execution of the proof?";
      CheckboxQuestion contractsQuestion = new CheckboxQuestion("appliedContracts", 
                                                                contractsTitle, 
                                                                true,
                                                                null, 
                                                                new NotUndefinedValueValidator("Question '" + contractsTitle + "' not answered."), 
                                                                true,
                                                                new Choice("None of the contracts was applied", "None"),
                                                                new Choice("Contract of method checkAndWithdraw(int)", "checkAndWithdraw"),
                                                                new Choice("Contract of method withdraw(int)", "withdraw", true),
                                                                new Choice("Contract of method canWithdraw(int)", "canWithdraw", true),
                                                                new Choice("Contract of method getBalance()", "getBalance"),
                                                                createGiveupAppliedContractsChoice());
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              new ProofAttemptJavaProjectModifier("Account",
                                                                  "checkAndWithdraw",
                                                                  new String[] {"I"},
                                                                  "checkAndWithdraw(int)",
                                                                  true,
                                                                  new FileDefinition("data/understandingProofAttempts/proofAccount/Account.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Account.proof", false),
                                                                  new FileDefinition("data/understandingProofAttempts/proofAccount/Account.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Account.java", true)),
                              new LabelQuestion("generalDescription", createGeneralDescription("Account#checkAndWithdraw(int)")),
                              openQuestion,
                              executedQuestion,
                              contractsQuestion);
   }

   private Choice createSomethingElseIsReasonChoice() {
      String reasonTitle = "What is the reason?";
      return new Choice("Something else is the reason why the proof is still open", 
                        "Something else", 
                        new TextQuestion("reason", reasonTitle, null, new NotUndefinedValueValidator("Question '" + reasonTitle + "' not answered."), false, 400, -1));
   }
   
   private TextQuestion createElseLocationSubQuestion() {
      String locationTitle = "Which location(s) have changed?";
      return new TextQuestion("changedLocation", locationTitle, null, new NotUndefinedValueValidator("Question '" + locationTitle + "' not answered."), false, 400, -1);
   }
   

   private TextQuestion createElseExceptionSubQuestion() {
      String exceptionTitle = "Which exception is thrown?";
      return new TextQuestion("thrownException", exceptionTitle, null, new NotUndefinedValueValidator("Question '" + exceptionTitle + "' not answered."), false, 400, -1);
   }

   private Choice createBugfreeChoice() {
      return new Choice("Code and specifications are bug free, proof can be closed interactively", "Bug free");
   }
   
   private Choice createGiveupWhyOpenChoice() {
      return new Choice("I tried my best to find out what (else) is wrong, but after 10 minutes I gave up.", "Give up");
   }
   
   private Choice createGiveupExecutedChoice() {
      return new Choice("I tried my best to find out what (else) is executed, but after 10 minutes I gave up.", "Give up");
   }
   
   private Choice createGiveupAppliedContractsChoice() {
      return new Choice("I tried my best to find out what (else) was applied, but after 10 minutes I gave up.", "Give up");
   }
   
   private Choice createGiveupLocationChoice() {
      return new Choice("I tried my best to find out what (else) has changed, but after 10 minutes I gave up.", "Give up");
   }
   
   private Choice createGiveupExceptionChoice() {
      return new Choice("I tried my best to find out what (else) can be thrown, but after 10 minutes I gave up.", "Give up");
   }
   
   private Choice createGiveupTerminationPathChoice() {
      return new Choice("I tried my best to find out at which execution path(s), but after 10 minutes I gave up.", "Give up");
   }


   private CheckboxQuestion createAccountLocationQuestion(String name) {
      String title = "Which not specified location(s) have changed?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("balance", "balance"),
                                  new Choice("amount", "amount"),
                                  new Choice("something else", "something else", createElseLocationSubQuestion()),
                                  new Choice("none", "none"),
                                  createGiveupLocationChoice());
   }
   
   private CheckboxQuestion createAccountTerminationQuestion(String name, boolean termination2expected) {
      String title = "At which execution path?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("Termination 1: canWithdraw(amount)", "Termination 1"),
                                  new Choice("Termination 2: !canWithdraw(amount)", "Termination 2", termination2expected),
                                  createGiveupTerminationPathChoice());
   }
   
   private String createGeneralDescription(String po) {
      return "Please inspect the current proof attempt of method '" + po + "' carefully and answer the following questions about it as best as possible.";
   }
   
   private QuestionPage createFeedbackPage() {
      List<Choice> choices = CollectionUtil.toList(new Choice("Very Helpful", "Very Helpful"), 
                                                   new Choice("Helpful", "Helpful"), 
                                                   new Choice("Little Helpful", "Little Helpful"), 
                                                   new Choice("Not Helpful", "Not Helpful"), 
                                                   new Choice("Never Used", "Never Used"));
      // KeY
      String proofTreeTitle = "Shown proof tree (tab 'Proof')";
      RadioButtonsQuestion proofTreeQuestion = new RadioButtonsQuestion("proofTree", 
                                                                        proofTreeTitle, 
                                                                        isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_PROOF_TREE) : null,
                                                                        false,
                                                                        null, 
                                                                        new NotUndefinedValueValidator("Question '" + proofTreeTitle + "' not answered."), 
                                                                        false,
                                                                        choices);
      String goalsTitle = "Shown goals  (tab 'Goals')";
      RadioButtonsQuestion goalsQuestion = new RadioButtonsQuestion("goals", 
                                                                    goalsTitle,
                                                                    isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_GOALS) : null,
                                                                    false,
                                                                    null, 
                                                                    new NotUndefinedValueValidator("Question '" + goalsTitle + "' not answered."), 
                                                                    false,
                                                                    choices);
      String sequentTitle = "Shown sequent";
      RadioButtonsQuestion sequentQuestion = new RadioButtonsQuestion("sequent", 
                                                                      sequentTitle, 
                                                                      isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_SEQUENT) : null,
                                                                      false,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + sequentTitle + "' not answered."), 
                                                                      false,
                                                                      choices);
      String hideTitle = "Hiding of intermediate proofsteps";
      RadioButtonsQuestion hideQuestion = new RadioButtonsQuestion("hideIntermediateProofsteps", 
                                                                   hideTitle, 
                                                                   isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_HIDE_ITERMEDIATE_STEPS) : null,
                                                                   false,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + hideTitle + "' not answered."), 
                                                                   false,
                                                                   choices);
//      String searchProofTreeTitle = "Search in proof tree";
//      RadioButtonsQuestion searchProofTreeQuestion = new RadioButtonsQuestion("searchProofTree", 
//                                                                              searchProofTreeTitle, 
//                                                                              false,
//                                                                              null, 
//                                                                              new NotUndefinedValueValidator("Question '" + searchProofTreeTitle + "' not answered."), 
//                                                                              false,
//                                                                              choices);
//      String searchSequentTitle = "Search in sequent";
//      RadioButtonsQuestion searchSequentQuestion = new RadioButtonsQuestion("searchSequent", 
//                                                                            searchSequentTitle, 
//                                                                            false,
//                                                                            null, 
//                                                                            new NotUndefinedValueValidator("Question '" + searchSequentTitle + "' not answered."), 
//                                                                            false,
//                                                                            choices);
      String listContractsTitle = "List of applied contracts";
      RadioButtonsQuestion listContractsQuestion = new RadioButtonsQuestion("listContracts", 
                                                                            listContractsTitle, 
                                                                            isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_APPLIED_CONTRACTS) : null,
                                                                            false,
                                                                            null, 
                                                                            new NotUndefinedValueValidator("Question '" + listContractsTitle + "' not answered."), 
                                                                            false,
                                                                            choices);
      SectionQuestion keySection = new SectionQuestion("KeY", "KeY", false, proofTreeQuestion, goalsQuestion, sequentQuestion, hideQuestion, listContractsQuestion);
      // SED
      String setTitle = "Shown symbolic execution tree";
      RadioButtonsQuestion setQuestion = new RadioButtonsQuestion("set", 
                                                                  setTitle, 
                                                                  isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_UP_SET) : null,
                                                                  false,
                                                                  null, 
                                                                  new NotUndefinedValueValidator("Question '" + setTitle + "' not answered."), 
                                                                  false,
                                                                  choices);
      String reachedTitle = "Highlighting of source code reached during symbolic execution";
      RadioButtonsQuestion reachedQuestion = new RadioButtonsQuestion("reachedSourceCode", 
                                                                      reachedTitle, 
                                                                      isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_UP_REACHED) : null,
                                                                      false,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + reachedTitle + "' not answered."), 
                                                                      false,
                                                                      choices);
      String variablesTitle = "Shown variables of a node (view 'Variables')";
      RadioButtonsQuestion variablesQuestion = new RadioButtonsQuestion("variables", 
                                                                        variablesTitle, 
                                                                        isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_UP_VARIABLES) : null,
                                                                        false,
                                                                        null, 
                                                                        new NotUndefinedValueValidator("Question '" + variablesTitle + "' not answered."), 
                                                                        false,
                                                                        choices);
      String layoutTitle = "Visualization of memory layouts";
      RadioButtonsQuestion layoutQuestion = new RadioButtonsQuestion("layouts", 
                                                                     layoutTitle, 
                                                                     isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_UP_MEMORY_LAYOUTS) : null,
                                                                     false,
                                                                     null, 
                                                                     new NotUndefinedValueValidator("Question '" + layoutTitle + "' not answered."), 
                                                                     false,
                                                                     choices);
      String truthTitle = "Truth value evaluation of postconditions, preconditions and loop invariants";
      RadioButtonsQuestion truthQuestion = new RadioButtonsQuestion("truth", 
                                                                    truthTitle, 
                                                                    isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_UP_TRUTH) : null,
                                                                    false,
                                                                    null, 
                                                                    new NotUndefinedValueValidator("Question '" + truthTitle + "' not answered."), 
                                                                    false,
                                                                    choices);
      SectionQuestion sedSection = new SectionQuestion("SED", "SED", false, setQuestion, reachedQuestion, variablesQuestion, layoutQuestion, truthQuestion);
      // KeY vs SED
      String keyVsSedTitle = "I prefer to inspect proofs with";
      RadioButtonsQuestion keyVsSedQuestion = new RadioButtonsQuestion("toolPreference", 
                                                                       keyVsSedTitle, 
                                                                       true,
                                                                       null, 
                                                                       new NotUndefinedValueValidator("Question '" + keyVsSedTitle + "' not answered."), 
                                                                       false,
                                                                       new Choice("KeY", "KeY"),
                                                                       new Choice("KeY and SED, both are equally good", "KeYandSEDequal"),
                                                                       new Choice("KeY and SED, depending on the proof", "KeYandSEDproof"),
                                                                       new Choice("KeY and SED, both are equally bad and should be improved", "KeYandSEDbad"),
                                                                       new Choice("SED", "SED"));
      SectionQuestion keyVsSedSection = new SectionQuestion("KeYvsSED", "KeY vs SED", false, keyVsSedQuestion);
      // Feedback
      SectionQuestion feedbackSection = new SectionQuestion("feedback", 
                                                            "Feedback", 
                                                            true, 
                                                            new TextQuestion("feedback", "Feedback about the tools or the evaluation (optional)", null, null, false, 400, 200));
      return new QuestionPage(FEEDBACK_PAGE,
                              "Feedback", 
                              "Please answer the question to give us some feeback about the tools and the evaluation.", 
                              false,
                              false,
                              null,
                              keySection,
                              sedSection,
                              keyVsSedSection,
                              feedbackSection);
   }

   protected String createPreconditionText(String precondition) {
      return "Precondition (" + precondition + ") not established";
   }

   protected String createPreconditionText(String precondition, String method) {
      return "Precondition (" + precondition + ") of " + method + " not established";
   }

   protected String createPostconditionText(String postcondition) {
      return "Postcondition (" + postcondition + ") does not hold";
   }

   protected String createPostconditionText(String postcondition, String method) {
      return "Postcondition (" + postcondition + ") of " + method + " does not hold";
   }

   protected String createMethodAssignableText() {
      return "Assignable clause of method contract violated";
   }

   protected String createLoopAssignableText() {
      return "Assignable clause of loop invariant violated";
   }

   protected String createMethodAssignableText(String postcondition, String method) {
      return "Assignable clause (" + postcondition + ") of method contract of " + method + " violated";
   }
   
   protected String createClassInvariantInitiallyText(String invariant) {
      return "Class Invariant (" + invariant + ") does not hold initially";
   }
   
   protected String createClassInvariantPreservedText(String invariant) {
      return "Class Invariant (" + invariant + ") is not preserved";
   }
   
   protected String createExceptionThrownText() {
      return "Exception is thrown (normal_behavior violated)";
   }
   
   protected String createExceptionThrownText(String method) {
      return "Exception is thrown (normal_behavior of " + method + " violated)";
   }
   
   protected String createLoopInvariantInitiallyText(String loopInvariant) {
      return "Loop invariant (" + loopInvariant + ") does not hold initially";
   }

   protected String createLoopInvariantPreservedText(String loopInvariant) {
      return "Loop invariant (" + loopInvariant + ") is not preserved by loop guard and loop body";
   }

   protected String createDecreasingText(String decreasingTerm) {
      return "Decreasing term (" + decreasingTerm + ") is not fulfilled by loop";
   }

   protected String createExceptionThrownValue() {
      return "Exception is thrown";
   }

   protected String createMethodAssignableValue() {
      return "Method assignable clause does not hold";
   }

   protected String createMethodAssignableValue(String method) {
      return method + ": " + createMethodAssignableValue();
   }

   protected String createLoopAssignableValue() {
      return "Loop invariant assignable clause does not hold";
   }

   protected String createPostconditionValue() {
      return "Postcondition does not hold";
   }
   
   protected String createPostconditionValue(String condition) {
      return condition + "postcondition does not hold";
   }

   protected String createPostconditionValue(String method, String condition) {
      return method + ": " + createPostconditionValue(condition);
   }

   protected String createPreconditionValue() {
      return "Precondition does not hold";
   }
   
   private String createPreconditionValue(String method) {
      return method + ": " + createPreconditionValue();
   }

   protected String createLoopInvariantInitiallyValue(String loopInvariant) {
      return "Loop invariant about " + loopInvariant + " does not hold initially";
   }

   protected String createLoopInvariantPreservedValue(String loopInvariant) {
      return "Loop invariant about " + loopInvariant + " is not preserved";
   }

   protected String createDecreasingValue() {
      return "Decreasing term is not fulfilled";
   }

   protected String createClassInvariantPreservedValue() {
      return "Class Invariant not preserved";
   }

   protected String createClassInvariantInitiallyValue() {
      return "Class Invariant does not hold";
   }

   protected String createQuestionPageMessage() {
      return "Please answer the questions to the best of your knowledge.";
   }

}
