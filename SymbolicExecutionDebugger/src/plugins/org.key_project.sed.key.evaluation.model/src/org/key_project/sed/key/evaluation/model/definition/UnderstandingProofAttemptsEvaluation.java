package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;
import java.util.List;

import org.key_project.sed.key.evaluation.model.Activator;
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
    * Page name of the JML introduction page.
    */
   public static final String JML_PAGE_NAME = "JML";

   /**
    * Page name of the summary page.
    */
   public static final String FEEDBACK_PAGE = "summary";


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
                                                                              true,
                                                                              "no", 
                                                                              new FixedValueValidator("yes", "Conditions are not accepted."), 
                                                                              false,
                                                                              new Choice("I &accept the conditions", "yes"), 
                                                                              new Choice("I do &not accept the conditions", "no")));
      QuestionPage backgroundPage = new QuestionPage("backgroundPage", 
                                                     "Background", 
                                                     "Please fill out the form with your background knowledge.",
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
                                                     new RadioButtonsQuestion("experienceWithKeY",
                                                                              "Experience with KeY", 
                                                                              true,
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with KeY not defined."), 
                                                                              false,
                                                                              new Choice("None", "None"), 
                                                                              new Choice("< 2 years", "Less than 2 years"), 
                                                                              new Choice(">= 2 years", "More than 2 years")),
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
                                                         "Confirm Sending Content", 
                                                         "Inspect the content to be send.", 
                                                         "Current date and time (nothing else!)");
      FixedForm introductionForm = new FixedForm("introductionForm", 
                                                 false,
                                                 new UnderstandingProofAttemptsRandomFormOrderComputer(),
                                                 conditionsPage, 
                                                 backgroundPage,
                                                 sendConditionsPage);
      // Create evaluation form
      URL jmlURL = Activator.getDefault().getBundle().getEntry("data/understandingProofAttempts/JML.html");
      InstructionPage jmlPage = new InstructionPage(JML_PAGE_NAME, "JML", "Read the JML introduction carefully before continuing.", jmlURL);
      ToolPage keyToolPage = new ToolPage(getTool(KEY_TOOL_NAME));
      ToolPage sedToolPage = new ToolPage(getTool(SED_TOOL_NAME));
      QuestionPage proof1Page = createCalendarQuestionPage(PROOF_1_PAGE_NAME, "Proof Attempt 1");
      QuestionPage proof2Page = createAccountQuestionPage(PROOF_2_PAGE_NAME, "Proof Attempt 2");
      QuestionPage proof3Page = createMinQuestionPage(PROOF_3_PAGE_NAME, "Proof Attempt 3");
      QuestionPage proof4Page = createMyIntegerQuestionPage(PROOF_4_PAGE_NAME, "Proof Attempt 4");
      QuestionPage feedbackPage = createFeedbackPage();
      SendFormPage sendEvaluationPage = new SendFormPage(SEND_EVALUATION_PAGE_NAME, 
                                                         "Confirm Sending Content", 
                                                         "Inspect the content to be send.", 
                                                         "Current date and time (nothing else!)");
      RandomForm evaluationForm = new RandomForm("evaluationForm", true, jmlPage, keyToolPage, sedToolPage, proof1Page, proof2Page, proof3Page, proof4Page, feedbackPage, sendEvaluationPage);
      // Create thanks form
      QuestionPage thanksPage = new QuestionPage("thanksPage", "Evaluation sucessfully completed", "Thank you for participating in the evaluation.", null);
      FixedForm thanksForm = new FixedForm("thanksForm", false, thanksPage);
      // Create forms
      return CollectionUtil.toList(introductionForm, evaluationForm, thanksForm);
   }

   protected QuestionPage createMyIntegerQuestionPage(String pageName, String title) {
      String howToCloseTitle = "How can the proof be closed?";
      CheckboxQuestion howToCloseQuestion = new CheckboxQuestion("howToClose", 
                                                                 howToCloseTitle, 
                                                                 true,
                                                                 null, 
                                                                 new NotUndefinedValueValidator("Question '" + howToCloseTitle + "' not answered."), 
                                                                 true,
                                                                 new Choice("Using the auto mode", "Using the auto mode"), 
                                                                 new Choice("Applying rules interactively", "Applying rules interactively"));
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
                                                               new Choice("summand.value", "summand.value"));
      String thrownExceptionTitle = "Which exception(s) are thrown?";
      CheckboxQuestion thrownExceptionQuestion = new CheckboxQuestion("whichExceptionsAreThrown", 
                                                                      thrownExceptionTitle, 
                                                                      true,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + thrownExceptionTitle + "' not answered."), 
                                                                      true,
                                                                      new Choice("java.lang.NullPointerException", "java.lang.NullPointerException"),
                                                                      new Choice("java.lang.ArithmeticException", "java.lang.ArithmeticException"),
                                                                      new Choice("java.lang.OutOfMemoryError", "java.lang.OutOfMemoryError"));
      String whyOpenTitle = "Why is the proof still open?";
      CheckboxQuestion whyOpenQuestion = new CheckboxQuestion("whyOpen", 
                                                              whyOpenTitle, 
                                                              true,
                                                              null, 
                                                              new NotUndefinedValueValidator("Question '" + whyOpenTitle + "' not answered."), 
                                                              true,
                                                              new Choice("Rule application stopped to early, proof is closeable", "Stopped to early", howToCloseQuestion), 
                                                              new Choice("Precondition (summand != null) is not established", "Precondition not established"),
                                                              new Choice("Postcondition (value == \\old(value) + summand.value) does not hold", "Postcondition does not hold"),
                                                              new Choice("Assignable clause does not hold", "Assignable clause does not hold", locationQuestion),
                                                              new Choice("Exception is thrown (normal_behavior violated)", "Exception is thrown", thrownExceptionQuestion));
      String openQuestionTitle = "Is the proof closed?";
      RadioButtonsQuestion openQuestion = new RadioButtonsQuestion("openOrClosed", 
                                                                   openQuestionTitle, 
                                                                   true,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + openQuestionTitle + "' not answered."), 
                                                                   true,
                                                                   new Choice("Yes", "Yes"), 
                                                                   new Choice("No", "No", whyOpenQuestion));
      String executedTitle = "Was statement (value += summand.value) at line 9 executed during symbolic execution of the proof?";
      RadioButtonsQuestion executedQuestion = new RadioButtonsQuestion("executedStatements", 
                                                                       executedTitle, 
                                                                       true,
                                                                       null, 
                                                                       new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                                       true,
                                                                       new Choice("Yes", "Yes"),
                                                                       new Choice("No", "No"));
      return new QuestionPage(pageName, 
                              title, 
                              "Please answer the question to the best of your knowledge.", 
                              new ProofAttemptJavaProjectModifier("MyInteger",
                                                                  "add",
                                                                  new String[] {"QMyInteger;"},
                                                                  new FileDefinition("data/understandingProofAttempts/proofMyInteger/MyInteger.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MyInteger.proof", false),
                                                                  new FileDefinition("data/understandingProofAttempts/proofMyInteger/MyInteger.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MyInteger.java", true)),
                              new LabelQuestion("generalDescription", createGeneralDescription("add(MyInteger)")),
                              openQuestion,
                              executedQuestion);
      // TODO: How to fix code or specifications?
   }
   
   protected QuestionPage createMinQuestionPage(String pageName, String title) {
      String howToCloseTitle = "How can the proof be closed?";
      CheckboxQuestion howToCloseQuestion = new CheckboxQuestion("howToClose", 
                                                                 howToCloseTitle, 
                                                                 true,
                                                                 null, 
                                                                 new NotUndefinedValueValidator("Question '" + howToCloseTitle + "' not answered."), 
                                                                 true,
                                                                 new Choice("Using the auto mode", "Using the auto mode"), 
                                                                 new Choice("Applying rules interactively", "Applying rules interactively"));
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
                                                                      new Choice("java.lang.OutOfMemoryError", "java.lang.OutOfMemoryError"));
      String whyOpenTitle = "Why is the proof still open?";
      CheckboxQuestion whyOpenQuestion = new CheckboxQuestion("whyOpen", 
                                                              whyOpenTitle, 
                                                              true,
                                                              null, 
                                                              new NotUndefinedValueValidator("Question '" + whyOpenTitle + "' not answered."), 
                                                              true,
                                                              new Choice("Rule application stopped to early, proof is closeable", "Stopped to early", howToCloseQuestion), 
                                                              new Choice("Precondition (array != null) is not established", "Precondition not established", createMinTerminationQuestion("preconditionTermination")),
                                                              new Choice("Postcondition (array == null || array.length == 0 ==> \\result == -1) does not hold", "Not found postcondition does not hold", createMinTerminationQuestion("postNotFoundTermination")),
                                                              new Choice("Postcondition (array != null && array.length >= 1 ==> (\\forall int i; i >= 0 && i < array.length; array[\\result] <= array[i])) does not hold", "Found postcondition does not hold", createMinTerminationQuestion("postFoundTermination")),
                                                              new Choice("Assignable clause of method contract does not hold", "Assignable clause of method contract does not hold", createMinLocationQuestion("whichMethodLocationsHaveChanged"), createMinTerminationQuestion("methodAssignableTermination")),
                                                              new Choice("Exception is thrown (normal_behavior violated)", "Exception is thrown", thrownExceptionQuestion),
                                                              new Choice("Loop invariant (i >= 1 && i <= array.length) does not hold initially", "Loop invariant about i does not hold initially", createMinTerminationQuestion("initialITermination")),
                                                              new Choice("Loop invariant (minIndex >= 0 && minIndex < i) does not hold initially", "Loop invariant about minIndex does not hold initially", createMinTerminationQuestion("initialMinIndexTermination")),
                                                              new Choice("Loop invariant (\\forall int j; j >= 0 && j < i; array[minIndex] <= array[j]) does not hold initially", "Loop invariant about array elements does not hold initially", createMinTerminationQuestion("initialArrayElementsTermination")),
                                                              new Choice("Loop invariant (i >= 1 && i <= array.length) is not preserved by loop guard and loop body", "Loop invariant about i is not preserved", createMinTerminationQuestion("preservedITermination")),
                                                              new Choice("Loop invariant (minIndex >= 0 && minIndex < i) is not preserved by loop guard and loop body", "Loop invariant about minIndex is not preserved", createMinTerminationQuestion("preservedMinIndexTermination")),
                                                              new Choice("Loop invariant (\\forall int j; j >= 0 && j < i; array[minIndex] <= array[j]) is not preserved by loop guard and loop body", "Loop invariant about array elements is not preserved", createMinTerminationQuestion("preservedArrayElementsTermination")),
                                                              new Choice("Decreasing term (array.length - i) is not fulfilled by loop", "Decreasing term is not fulfilled", createMinTerminationQuestion("decreasingTermination")),
                                                              new Choice("Assignable clause of loop does not hold", "Assignable clause of loop does not hold", createMinLocationQuestion("whichLoopLocationsHaveChanged"), createMinTerminationQuestion("loopAssignableTermination")));
      String openQuestionTitle = "Is the proof closed?";
      RadioButtonsQuestion openQuestion = new RadioButtonsQuestion("openOrClosed", 
                                                                   openQuestionTitle, 
                                                                   true,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + openQuestionTitle + "' not answered."), 
                                                                   true,
                                                                   new Choice("Yes", "Yes"), 
                                                                   new Choice("No", "No", whyOpenQuestion));
      String executedTitle = "Which statement(s) are executed at least once during symbolic execution of the proof?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements was executed", "None"),
                                                               new Choice("Line 8 (if (array != null))", "Line 8"),
                                                               new Choice("Line 9 (if (array.length == 0))", "Line 9"),
                                                               new Choice("Line 10 (return -1)", "Line 10"),
                                                               new Choice("Line 12 (array.length == 1)", "Line 12"),
                                                               new Choice("Line 13 (return array[0])", "Line 13"),
                                                               new Choice("Line 16 (int minIndex = 0)", "Line 16"),
                                                               new Choice("Line 24 (int i = 1)", "Line 24 initial"),
                                                               new Choice("Line 24 (i < array.length)", "Line 24 condition"),
                                                               new Choice("Line 24 (i++)", "Line 24 update"),
                                                               new Choice("Line 25 (if (array[i] < array[minIndex]))", "Line 25"),
                                                               new Choice("Line 26 (minIndex = 1)", "Line 26"),
                                                               new Choice("Line 33 (return minIndex)", "Line 33"),
                                                               new Choice("Line 37 (return -1)", "Line 37"));
      return new QuestionPage(pageName, 
                              title, 
                              "Please answer the question to the best of your knowledge.", 
                              new ProofAttemptJavaProjectModifier("ArrayUtil",
                                                                  "minIndex",
                                                                  new String[] {"[I"},
                                                                  new FileDefinition("data/understandingProofAttempts/proofMin/ArrayUtil.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ArrayUtil.proof", false),
                                                                  new FileDefinition("data/understandingProofAttempts/proofMin/ArrayUtil.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ArrayUtil.java", true)),
                              new LabelQuestion("generalDescription", createGeneralDescription("minIndex(int[])")),
                              openQuestion,
                              executedQuestion);
      // TODO: How to fix code or specifications?
   }
   
   protected CheckboxQuestion createMinLocationQuestion(String name) {
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
                                  new Choice("i", "i"));
   }
   
   protected CheckboxQuestion createMinTerminationQuestion(String name) {
      String title = "At which execution path?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("Return 1 (array != null & array.length == 0)", "Return 1"),
                                  new Choice("Return 2 (array != null & array.length == 1)", "Return 2"),
                                  new Choice("Return 3 (array != null & array.length > 1)", "Return 3"),
                                  new Choice("Return 4 (array == null)", "Return 4"),
                                  new Choice("Loop End 1 (array[i] < array[minIndex])", "Loop End 1"),
                                  new Choice("Loop End 2 (array[i] >= array[minIndex])", "Loop End 2"));
   }
   
   protected QuestionPage createCalendarQuestionPage(String pageName, String title) {
      String howToCloseTitle = "How can the proof be closed?";
      CheckboxQuestion howToCloseQuestion = new CheckboxQuestion("howToClose", 
                                                                 howToCloseTitle, 
                                                                 true,
                                                                 null, 
                                                                 new NotUndefinedValueValidator("Question '" + howToCloseTitle + "' not answered."), 
                                                                 true,
                                                                 new Choice("Using the auto mode", "Using the auto mode"), 
                                                                 new Choice("Applying rules interactively", "Applying rules interactively"));
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
                                                                      new Choice("java.lang.OutOfMemoryError", "java.lang.OutOfMemoryError"));
      String whyOpenTitle = "Why is the proof still open?";
      CheckboxQuestion whyOpenQuestion = new CheckboxQuestion("whyOpen", 
                                                              whyOpenTitle, 
                                                              true,
                                                              null, 
                                                              new NotUndefinedValueValidator("Question '" + whyOpenTitle + "' not answered."), 
                                                              true,
                                                              new Choice("Rule application stopped to early, proof is closeable", "Stopped to early", howToCloseQuestion), 
                                                              new Choice("Precondition (entry != null) is not established", "Precondition not established", createCalendarTerminationQuestion("preconditionTermination")),
                                                              new Choice("Invariant (entrySize >= 0 && entrySize < entries.length) is not established", "Invariant not established", createCalendarTerminationQuestion("invariantEstablishedTermination")),
                                                              new Choice("Postcondition (entries[\\old(entrySize)] == entry) does not hold", "Postcondition about entry does not hold", createCalendarTerminationQuestion("postEntryTermination")),
                                                              new Choice("Postcondition (entrySize == \\old(entrySize) + 1) does not hold", "Postcondition about entrySize does not hold", createCalendarTerminationQuestion("postEntrySizeTermination")),
                                                              new Choice("Invariant (entrySize >= 0 && entrySize < entries.length) is not preserved", "Invariant not preserved", createCalendarTerminationQuestion("invariantNotPreservedTermination")),
                                                              new Choice("Assignable clause does not hold", "Assignable clause does not hold", createCalendarLocationQuestion("whichMethodLocationsHaveChanged"), createCalendarTerminationQuestion("assignableTermination")),
                                                              new Choice("Exception is thrown (normal_behavior violated)", "Exception is thrown", thrownExceptionQuestion),
                                                              new Choice("Loop invariant (i >= 0 && i <= entries.length) does not hold initially", "Loop invariant about i does not hold initially", createCalendarTerminationQuestion("loopInvariantIInitialTermination")),
                                                              new Choice("Loop invariant (\\forall int j; j >= 0 && j < i; newEntries[j] == entries[j]) does not hold initially", "Loop invariant about array elements does not hold initially", createCalendarTerminationQuestion("loopInvariantArrayElementsInitialTermination")),
                                                              new Choice("Loop invariant (i >= 0 && i <= entries.length) is not preserved by loop guard and loop body", "Loop invariant about i is not preserved", createCalendarTerminationQuestion("loopInvariantIPreservedTermination")),
                                                              new Choice("Loop invariant (\\forall int j; j >= 0 && j < i; newEntries[j] == entries[j]) is not preserved by loop guard and loop body", "Loop invariant about array elements is not preserved", createCalendarTerminationQuestion("loopInvariantArrayElementsPreservedTermination")),
                                                              new Choice("Decreasing term (entries.length - i) is not fulfilled by loop", "Decreasing term is not fulfilled", createCalendarTerminationQuestion("decreasingTermination")),
                                                              new Choice("Assignable clause of loop does not hold", "Assignable clause of loop does not hold", createCalendarLocationQuestion("whichLoopLocationsHaveChanged"), createCalendarTerminationQuestion("loopAssingableTermination")));
      String openQuestionTitle = "Is the proof closed?";
      RadioButtonsQuestion openQuestion = new RadioButtonsQuestion("openOrClosed", 
                                                                   openQuestionTitle, 
                                                                   true,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + openQuestionTitle + "' not answered."), 
                                                                   true,
                                                                   new Choice("Yes", "Yes"), 
                                                                   new Choice("No", "No", whyOpenQuestion));
      String executedTitle = "Which statement(s) are executed at least once during symbolic execution of the proof?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements was executed", "None"),
                                                               new Choice("Line 14 (if (entrySize == entries.length))", "Line 14"),
                                                               new Choice("Line 15 (Entry[] newEntries = new Entry[entries.length * 2])", "Line 15"),
                                                               new Choice("Line 22 (int i = 0)", "Line 22 initial"),
                                                               new Choice("Line 22 (i < entries.length)", "Line 22 condition"),
                                                               new Choice("Line 22 (i++)", "Line 22 update"),
                                                               new Choice("Line 23 (newEntries[i] = entries[i])", "Line 23"),
                                                               new Choice("Line 25 (entries = newEntries)", "Line 25"),
                                                               new Choice("Line 27 (entries[entrySize] = entry)", "Line 27"),
                                                               new Choice("Line 28 (entrySize++)", "Line 28"));
      return new QuestionPage(pageName, 
                              title, 
                              "Please answer the question to the best of your knowledge.", 
                              new ProofAttemptJavaProjectModifier("MyInteger",
                                                                  "add",
                                                                  new String[] {"QMyInteger;"},
                                                                  new FileDefinition("data/understandingProofAttempts/proofCalendar/Calendar.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Calendar.proof", false),
                                                                  new FileDefinition("data/understandingProofAttempts/proofCalendar/Calendar.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Calendar.java", true)),
                              new LabelQuestion("generalDescription", createGeneralDescription("addEntry(Entry)")),
                              openQuestion,
                              executedQuestion);
      // TODO: How to fix code or specifications?
   }
   
   protected CheckboxQuestion createCalendarLocationQuestion(String name) {
      String title = "Which not specified location(s) have changed?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("None of the statements was executed", "None"),
                                  new Choice("entries", "entries"),
                                  new Choice("entries[entrySize]", "entries[entrySize]"),
                                  new Choice("entries[*]", "entries[*]"),
                                  new Choice("entries.length", "entries.length"),
                                  new Choice("entrySize", "entrySize"),
                                  new Choice("i", "i"),
                                  new Choice("newEntries", "newEntries"),
                                  new Choice("newEntries.length", "newEntries.length"),
                                  new Choice("newEntries[*]", "newEntries[*]"));
   }
   
   protected CheckboxQuestion createCalendarTerminationQuestion(String name) {
      String title = "At which execution path?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("After Then (entrySize == entries.length)", "After Then"),
                                  new Choice("After Else (entrySize != entries.length)", "After Else"),
                                  new Choice("Loop End", "Loop End"));
   }
   
   public RandomForm getEvaluationForm() {
      return (RandomForm) getForm("evaluationForm");
   }
   

   protected QuestionPage createAccountQuestionPage(String pageName, String title) {
      String howToCloseTitle = "How can the proof be closed?";
      CheckboxQuestion howToCloseQuestion = new CheckboxQuestion("howToClose", 
                                                                 howToCloseTitle, 
                                                                 true,
                                                                 null, 
                                                                 new NotUndefinedValueValidator("Question '" + howToCloseTitle + "' not answered."), 
                                                                 true,
                                                                 new Choice("Using the auto mode", "Using the auto mode"), 
                                                                 new Choice("Applying rules interactively", "Applying rules interactively"));
      String thrownExceptionTitle = "Which exception(s) are thrown?";
      CheckboxQuestion thrownExceptionQuestion = new CheckboxQuestion("whichExceptionsAreThrown", 
                                                                      thrownExceptionTitle, 
                                                                      true,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + thrownExceptionTitle + "' not answered."), 
                                                                      true,
                                                                      new Choice("java.lang.NullPointerException", "java.lang.NullPointerException"),
                                                                      new Choice("java.lang.ArithmeticException", "java.lang.ArithmeticException"),
                                                                      new Choice("java.lang.IllegalArgumentException", "java.lang.IllegalArgumentException"),
                                                                      new Choice("java.lang.IllegalStateException", "java.lang.IllegalStateException"),
                                                                      new Choice("java.lang.invoke.WrongMethodTypeException", "java.lang.invoke.WrongMethodTypeException"),
                                                                      new Choice("javax.naming.OperationNotSupportedException", "javax.naming.OperationNotSupportedException"),
                                                                      new Choice("java.lang.OutOfMemoryError", "java.lang.OutOfMemoryError"));
      String whyOpenTitle = "Why is the proof still open?";
      CheckboxQuestion whyOpenQuestion = new CheckboxQuestion("whyOpen", 
                                                              whyOpenTitle, 
                                                              true,
                                                              null, 
                                                              new NotUndefinedValueValidator("Question '" + whyOpenTitle + "' not answered."), 
                                                              true,
                                                              new Choice("Rule application stopped to early, proof is closeable", "Stopped to early", howToCloseQuestion), 
                                                              new Choice("Precondition (amount > 0) of checkAndWithdraw(int) is not established", "checkAndWithdraw: Precondition not established", createAccountTerminationQuestion("checkAndWithdrawPreTermination")),
                                                              new Choice("Postcondition (balance == \\old(balance) - \\result) of checkAndWithdraw(int) does not hold", "checkAndWithdraw: Postcondition about balance does not hold", createAccountTerminationQuestion("checkAndWithdrawPostconditionBalanceTermination")),
                                                              new Choice("Postcondition (\\result == amount) of checkAndWithdraw(int) does not hold", "checkAndWithdraw: Postcondition about result does not hold", createAccountTerminationQuestion("checkAndWithdrawPostcondtionResultTermination")),
                                                              new Choice("Assignable clause (balance) of method contract of checkAndWithdraw(int) does not hold", "checkAndWithdraw: Assignable clause of method contract does not hold", createAccountLocationQuestion("checkAndWithdrawLocations"), createAccountTerminationQuestion("checkAndWithdrawAssignableTermination")),

                                                              new Choice("Precondition (amount > 0) of withdraw(int) is not established", "withdraw: Precondition not established", createAccountTerminationQuestion("withdrawPreconditionTermination")),
                                                              new Choice("Postcondition (balance == \\old(balance) - amount) of withdraw(int) does not hold", "withdraw: Postcondition about balance does not hold", createAccountTerminationQuestion("withdrawPostconditionTermination")),
                                                              new Choice("Assignable clause (balance) of method contract of withdraw(int) does not hold", "withdraw: Assignable clause of method contract does not hold", createAccountLocationQuestion("withdrawLocations"), createAccountTerminationQuestion("withdrawAssignableTermination")),

                                                              new Choice("Precondition (amount > 0) of canWithdraw(int) is not established", "canWithdraw: Precondition not established", createAccountTerminationQuestion("canWithdrawPreconditionTermination")),
                                                              new Choice("Postcondition (true) of canWithdraw(int) does not hold", "canWithdraw: Postcondition about balance does not hold", createAccountTerminationQuestion("canWithdrawPostconditionTermination")),
                                                              new Choice("Assignable clause (\\nothing) of method contract of canWithdraw(int) does not hold", "canWithdraw: Assignable clause of method contract does not hold", createAccountLocationQuestion("canWithdrawLocations"), createAccountTerminationQuestion("canWithdrawAssignableTermination")),

                                                              new Choice("Precondition (true) of getBalance() is not established", "getBalance: Precondition not established", createAccountTerminationQuestion("getBalancePreconditionTermination")),
                                                              new Choice("Postcondition (\result == balance) of getBalance() does not hold", "getBalance: Postcondition about balance does not hold", createAccountTerminationQuestion("getBalancePostconditionTermination")),
                                                              new Choice("Assignable clause (\\nothing) of method contract of getBalance(int) does not hold", "getBalance: Assignable clause of method contract does not hold", createAccountLocationQuestion("getBalanceLocations"), createAccountTerminationQuestion("getBalanceAssignableTermination")),
                                                              
                                                              new Choice("Exception is thrown (normal_behavior violated)", "Exception is thrown", thrownExceptionQuestion));
      String openQuestionTitle = "Is the proof closed?";
      RadioButtonsQuestion openQuestion = new RadioButtonsQuestion("openOrClosed", 
                                                                   openQuestionTitle, 
                                                                   true,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + openQuestionTitle + "' not answered."), 
                                                                   true,
                                                                   new Choice("Yes", "Yes"), 
                                                                   new Choice("No", "No", whyOpenQuestion));
      String executedTitle = "Which statement(s) are executed at least once during symbolic execution of the proof?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements was executed", "None"),
                                                               new Choice("Line 11 (if (canWithdraw(amount)))", "Line 10"),
                                                               new Choice("Line 12 (withdraw(amount))", "Line 11"),
                                                               new Choice("Line 13 (return amount)", "Line 12"),
                                                               new Choice("Line 16 (return 0)", "Line 15"),
                                                               new Choice("Line 26 (balance -= amount)", "Line 25"),
                                                               new Choice("Line 35 (return amount > 0)", "Line 32"),
                                                               new Choice("Line 44 (return balance)", "Line 39"));
      String contractsTitle = "Which method contracts are applied at least once during symbolic execution of the proof?";
      CheckboxQuestion contractsQuestion = new CheckboxQuestion("appliedContracts", 
                                                                contractsTitle, 
                                                                true,
                                                                null, 
                                                                new NotUndefinedValueValidator("Question '" + contractsTitle + "' not answered."), 
                                                                true,
                                                                new Choice("None of the contracts was applied", "None"),
                                                                new Choice("Contract of method checkAndWithdraw(int)", "checkAndWithdraw"),
                                                                new Choice("Contract of method withdraw(int)", "withdraw"),
                                                                new Choice("Contract of method canWithdraw(int)", "canWithdraw"),
                                                                new Choice("Contract of method getBalance()", "getBalance"));
      return new QuestionPage(pageName, 
                              title, 
                              "Please answer the question to the best of your knowledge.", 
                              new ProofAttemptJavaProjectModifier("MyInteger",
                                                                  "add",
                                                                  new String[] {"QMyInteger;"},
                                                                  new FileDefinition("data/understandingProofAttempts/proofAccount/Account.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Account.proof", false),
                                                                  new FileDefinition("data/understandingProofAttempts/proofAccount/Account.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Account.java", true)),
                              new LabelQuestion("generalDescription", createGeneralDescription("checkAndWithdraw(int)")),
                              openQuestion,
                              executedQuestion,
                              contractsQuestion);
      // TODO: How to fix code or specifications?
      // TODO: Question about not fulfilled pre/post conditions
   }
   
   protected CheckboxQuestion createAccountLocationQuestion(String name) {
      String title = "Which not specified location(s) have changed?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("balance", "balance"),
                                  new Choice("amount", "amount"));
   }
   
   protected CheckboxQuestion createAccountTerminationQuestion(String name) {
      String title = "At which execution path?";
      return new CheckboxQuestion(name, 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("Return 1 (canWithdraw(amount))", "Return amount"),
                                  new Choice("Return 2 (!canWithdraw(amount))", "Return 0"));
   }
   
   protected String createGeneralDescription(String po) {
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
                                                                        false,
                                                                        null, 
                                                                        new NotUndefinedValueValidator("Question '" + proofTreeTitle + "' not answered."), 
                                                                        false,
                                                                        choices);
      String goalsTitle = "Shown goals  (tab 'Goals')";
      RadioButtonsQuestion goalsQuestion = new RadioButtonsQuestion("goals", 
                                                                    goalsTitle, 
                                                                    false,
                                                                    null, 
                                                                    new NotUndefinedValueValidator("Question '" + goalsTitle + "' not answered."), 
                                                                    false,
                                                                    choices);
      String sequentTitle = "Shown sequent";
      RadioButtonsQuestion sequentQuestion = new RadioButtonsQuestion("sequent", 
                                                                      sequentTitle, 
                                                                      false,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + sequentTitle + "' not answered."), 
                                                                      false,
                                                                      choices);
      String hideTitle = "Hiding of intermediate proofsteps";
      RadioButtonsQuestion hideQuestion = new RadioButtonsQuestion("hideIntermediateProofsteps", 
                                                                   hideTitle, 
                                                                   false,
                                                                   null, 
                                                                   new NotUndefinedValueValidator("Question '" + hideTitle + "' not answered."), 
                                                                   false,
                                                                   choices);
      String searchProofTreeTitle = "Search in proof tree";
      RadioButtonsQuestion searchProofTreeQuestion = new RadioButtonsQuestion("searchProofTree", 
                                                                              searchProofTreeTitle, 
                                                                              false,
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Question '" + searchProofTreeTitle + "' not answered."), 
                                                                              false,
                                                                              choices);
      String searchSequentTitle = "Search in sequent";
      RadioButtonsQuestion searchSequentQuestion = new RadioButtonsQuestion("searchSequent", 
                                                                            searchSequentTitle, 
                                                                            false,
                                                                            null, 
                                                                            new NotUndefinedValueValidator("Question '" + searchSequentTitle + "' not answered."), 
                                                                            false,
                                                                            choices);
      SectionQuestion keySection = new SectionQuestion("KeY", "KeY", false, proofTreeQuestion, goalsQuestion, sequentQuestion, hideQuestion, searchProofTreeQuestion, searchSequentQuestion);
      // SED
      String setTitle = "Show symbolic execution tree";
      RadioButtonsQuestion setQuestion = new RadioButtonsQuestion("set", 
                                                                  setTitle, 
                                                                  false,
                                                                  null, 
                                                                  new NotUndefinedValueValidator("Question '" + setTitle + "' not answered."), 
                                                                  false,
                                                                  choices);
      String variablesTitle = "Shown variables of a node (view 'Variables')";
      RadioButtonsQuestion variablesQuestion = new RadioButtonsQuestion("variables", 
                                                                        variablesTitle, 
                                                                        false,
                                                                        null, 
                                                                        new NotUndefinedValueValidator("Question '" + variablesTitle + "' not answered."), 
                                                                        false,
                                                                        choices);
      String layoutTitle = "Visualization of memory layouts";
      RadioButtonsQuestion layoutQuestion = new RadioButtonsQuestion("layouts", 
                                                                     layoutTitle, 
                                                                     false,
                                                                     null, 
                                                                     new NotUndefinedValueValidator("Question '" + layoutTitle + "' not answered."), 
                                                                     false,
                                                                     choices);
      String truthTitle = "Truth value evaluation";
      RadioButtonsQuestion truthQuestion = new RadioButtonsQuestion("truth", 
                                                                    truthTitle, 
                                                                    false,
                                                                    null, 
                                                                    new NotUndefinedValueValidator("Question '" + truthTitle + "' not answered."), 
                                                                    false,
                                                                    choices);
      SectionQuestion sedSection = new SectionQuestion("SED", "SED", false, setQuestion, variablesQuestion, layoutQuestion, truthQuestion);
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
                                                                       new Choice("SED", "SED"));
      SectionQuestion keyVsSedSection = new SectionQuestion("KeYvsSED", "KeY vs SED", false, keyVsSedQuestion);
      // Feedback
      SectionQuestion feedbackSection = new SectionQuestion("feedback", 
                                                            "Feedback", 
                                                            true, 
                                                            new TextQuestion("feedback", "Feedback about the tools or the evaluation (optional)", null, null, false));
      return new QuestionPage(FEEDBACK_PAGE,
                              "Feedback", 
                              "Please answer the question to give us some feeback about the tools and the evaluation.", 
                              null,
                              keySection,
                              sedSection,
                              keyVsSedSection,
                              feedbackSection);
   }
}
