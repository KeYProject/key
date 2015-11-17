package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;
import java.util.Collections;
import java.util.List;

import org.key_project.sed.key.evaluation.model.tooling.JavaProjectModifier;
import org.key_project.sed.key.evaluation.model.tooling.JavaProjectModifier.FileDefinition;
import org.key_project.sed.key.evaluation.model.tooling.ReviewingCodeJavaProjectModifier;
import org.key_project.sed.key.evaluation.model.tooling.ReviewingCodeJavaProjectModifier.ProofFileFileDefinition;
import org.key_project.sed.key.evaluation.model.util.EvaluationModelImages;
import org.key_project.sed.key.evaluation.model.validation.FixedValueValidator;
import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.sed.key.evaluation.model.validation.NotUndefinedValueValidator;
import org.key_project.util.java.CollectionUtil;

public class ReviewingCodeEvaluation extends AbstractEvaluation {
   /**
    * If this flag is {@code true} the participant can choose between 4 or 6 examples.
    */
   public static final boolean SHORT_EVALUATION_ENABLED = true;
   
   /**
    * If this flag is {@code true} the evaluation will ask for changed locations.
    */
   public static final boolean ASK_FOR_CHANGED_LOCATIONS = false;
   
   /**
    * The only instance of this class.
    */
   public static final ReviewingCodeEvaluation INSTANCE = new ReviewingCodeEvaluation();

   /**
    * The name of the {@link Tool} representing no tools.
    */
   public static final String NO_TOOL_NAME = "Direct Code Review";

   /**
    * The name of the {@link Tool} representing 'SED'.
    */
   public static final String SED_TOOL_NAME = "SED";

   /**
    * The name of the introduction form.
    */
   public static final String INTRODUCTION_FORM_NAME = "introductionForm";
   
   /**
    * The name of the extend page.
    */
   public static final String EXTEND_PAGE_NAME = "extentPage";

   /**
    * The name of the used random order computer.
    */
   public static final String RANDOM_COMPUTER_NAME = "ReviewingCodeRandomFormOrderComputer";

   /**
    * Page name of the evaluation instruction page.
    */
   public static final String EVALUATION_PAGE_NAME = "evaluationInstructions";

   /**
    * Page name of the JML introduction page.
    */
   public static final String JML_PAGE_NAME = "JML";
   
   /**
    * Page name of example 1.
    */
   public static final String EXAMPLE_1_PAGE_NAME = "ObservableArray";

   /**
    * Page name of example 2.
    */
   public static final String EXAMPLE_2_PAGE_NAME = "BankUtil";

   /**
    * Page name of example 3.
    */
   public static final String EXAMPLE_3_PAGE_NAME = "IntegerUtil";

   /**
    * Page name of example 4.
    */
   public static final String EXAMPLE_4_PAGE_NAME = "MathUtil";

   /**
    * Page name of example 5.
    */
   public static final String EXAMPLE_5_PAGE_NAME = "ValueSearch";

   /**
    * Page name of example 6.
    */
   public static final String EXAMPLE_6_PAGE_NAME = "Stack";

   /**
    * Page name of the send evaluation page.
    */
   public static final String SEND_EVALUATION_PAGE_NAME = "sendEvaluation";

   /**
    * The name of the evaluation form.
    */
   public static final String EVALUATION_FORM_NAME = "evaluationForm";

   /**
    * Page name of the summary page.
    */
   public static final String FEEDBACK_PAGE = "feedback";

   /**
    * Question name of the question defining the number of examples.
    */
   public static final String NUMBER_OF_EXAMPLES_QUESTION = "numberOfExamples";

   /**
    * Value of choice defining 4 examples.
    */
   public static final String FOUR_EXAMPLES_CHOICE_VALUE = "4 Examples";
   
   /**
    * Forbid additional instances.
    */
   private ReviewingCodeEvaluation() {
      super("Reviewing Code", isUIAvailable() ? "data/reviewingCode/instructions/" : null);
   }
   
   @Override
   protected List<Tool> computeTools() {
      URL noToolURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/NO_TOOLScreencast.html") : null;
      URL noToolWizardURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/NO_TOOLScreencastWizard.html") : null;
      URL sedURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/SED-Screencast.html") : null;
      URL sedWizardURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/SED-ScreencastWizard.html") : null;
      Tool noTool = new Tool(NO_TOOL_NAME, 
                             noToolURL, 
                             noToolWizardURL, 
                             isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.JAVA_APPLICATION_LOGO) : null);
      Tool sed = new Tool(SED_TOOL_NAME, 
                          sedURL, 
                          sedWizardURL, 
                          isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_LOGO) : null);
      return CollectionUtil.toList(noTool, sed);
   }

   @Override
   protected List<AbstractForm> computeForms() {
      // Create introduction form
      URL conditionsURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/conditions.html") : null;
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
      QuestionPage backgroundPage = new QuestionPage("backgroundPage", 
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
                                                     new RadioButtonsQuestion("experienceWithSymbolicExecution",
                                                                              "Experience with symbolic execution (e.g. verification or test case generation)", 
                                                                              true,
                                                                              null, 
                                                                              new NotUndefinedValueValidator("Experience with symbolic execution not defined."), 
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
      QuestionPage extendPage = new QuestionPage(EXTEND_PAGE_NAME, 
                                                 "Evaluation Extent", 
                                                 "Please define the extent of the evaluation.",
                                                 true,
                                                 true,
                                                 false,
                                                 SHORT_EVALUATION_ENABLED,
                                                 null,
                                                 new RadioButtonsQuestion(NUMBER_OF_EXAMPLES_QUESTION,
                                                                          "Number of examples", 
                                                                          true,
                                                                          "6 Examples", 
                                                                          new NotUndefinedValueValidator("Number of examples"), 
                                                                          false,
                                                                          new Choice("4 Examples (45 to 60 minutes)", FOUR_EXAMPLES_CHOICE_VALUE), 
                                                                          new Choice("6 Examples (45 to 90 minutes)", "6 Examples")));
      SendFormPage sendConditionsPage = new SendFormPage("sendConditions", 
                                                         "Confirm Sending Background Knowledge (used to order proof attempts)", 
                                                         "Optionally, inspect the answers to be sent.", 
                                                         "Current date and time (nothing else!)");
      FixedForm introductionForm = new FixedForm(INTRODUCTION_FORM_NAME, 
                                                 false,
                                                 RANDOM_COMPUTER_NAME,
                                                 conditionsPage, 
                                                 backgroundPage,
                                                 extendPage,
                                                 sendConditionsPage);
      // Create evaluation form
      URL evaluationURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/EvaluationIntroduction-Screencast.html") : null;
      URL jmlURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/JML.html") : null;
      InstructionPage evaluationPage = new InstructionPage(EVALUATION_PAGE_NAME, "Evaluation Instructions", "Read the evaluation instructions carefully before continuing.", evaluationURL, isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.EVALUATION) : null);
      InstructionPage jmlPage = new InstructionPage(JML_PAGE_NAME, "JML", "Read the JML introduction carefully before continuing.", jmlURL, isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.JML_LOGO) : null);
      ToolPage noToolPage = new ToolPage(getTool(NO_TOOL_NAME),
                                         new ReviewingCodeJavaProjectModifier("Database", 
                                                                              false, 
                                                                              null,
                                                                              new ProofFileFileDefinition[] {new ProofFileFileDefinition("data/reviewingCode/instructions-archived/instructionExample/accumulateDatabase.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/accumulateDatabase.proof", false, "Database", "accumulateDatabase", new String[] {"QAccumulator;"})},
                                                                              null,
                                                                              new FileDefinition("data/reviewingCode/instructions-archived/instructionExample/Database.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Database.java", true)),
                                         false);
            
      ToolPage sedToolPage = new ToolPage(getTool(SED_TOOL_NAME),
                                          new ReviewingCodeJavaProjectModifier("Database", 
                                                                               false, 
                                                                               null,
                                                                               new ProofFileFileDefinition[] {new ProofFileFileDefinition("data/reviewingCode/instructions-archived/instructionExample/accumulateDatabase.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/accumulateDatabase.proof", false, "Database", "accumulateDatabase", new String[] {"QAccumulator;"})},
                                                                               null,
                                                                               new FileDefinition("data/reviewingCode/instructions-archived/instructionExample/Database.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Database.java", true)),
                                          false);
      QuestionPage example1Page = createObservableArrayQuestionPage(EXAMPLE_1_PAGE_NAME, "Review of cass ObservableArray");
      QuestionPage example2Page = createBankUtilQuestionPage(EXAMPLE_2_PAGE_NAME, "Review of class BankUtil");
      QuestionPage example3Page = createIntegerUtilQuestionPage(EXAMPLE_3_PAGE_NAME, "Review of class IntegerUtil");
      QuestionPage example4Page = createMathUtilQuestionPage(EXAMPLE_4_PAGE_NAME, "Review of class MathUtil");
      QuestionPage example5Page = createValueSearchQuestionPage(EXAMPLE_5_PAGE_NAME, "Review of class ValueSearch");
      QuestionPage example6Page = createStackQuestionPage(EXAMPLE_6_PAGE_NAME, "Review of class Stack");
      QuestionPage feedbackPage = createFeedbackPage();
      SendFormPage sendEvaluationPage = new SendFormPage(SEND_EVALUATION_PAGE_NAME, 
                                                         "Confirm Sending Evaluation Answers", 
                                                         "Optionally, inspect the answers to be sent.", 
                                                         "Current date and time (nothing else!)");
      RandomForm evaluationForm = new RandomForm(EVALUATION_FORM_NAME, true, evaluationPage, jmlPage, noToolPage, sedToolPage, example1Page, example2Page, example3Page, example4Page, example5Page, example6Page, feedbackPage, sendEvaluationPage);
      // Create thanks form
      QuestionPage thanksPage = new QuestionPage("thanksPage", 
                                                 "Evaluation sucessfully completed", 
                                                 "Thank you for participating in the evaluation.", 
                                                 false, 
                                                 false,
                                                 null,
                                                 new ImageQuestion("thanksImage", isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_THANKS, 25) : null));
      FixedForm thanksForm = new FixedForm("thanksForm", false, thanksPage);
      return CollectionUtil.toList(introductionForm, evaluationForm, thanksForm);
   }

   
   
   
   
   
   
   private QuestionPage createFeedbackPage() {
      List<Choice> choices = CollectionUtil.toList(new Choice("Very Helpful", "Very Helpful"), 
                                                   new Choice("Helpful", "Helpful"), 
                                                   new Choice("Little Helpful", "Little Helpful"), 
                                                   new Choice("Not Helpful", "Not Helpful"), 
                                                   new Choice("Never Used", "Never Used"));
      // SED
      String setTitle = "Shown symbolic execution tree";
      RadioButtonsQuestion setQuestion = new RadioButtonsQuestion("set", 
                                                                  setTitle, 
                                                                  isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_RC_SET) : null,
                                                                  false,
                                                                  null, 
                                                                  new NotUndefinedValueValidator("Question '" + setTitle + "' not answered."), 
                                                                  false,
                                                                  choices);
      String nodePropertiesTitle = "Properties of selected node";
      RadioButtonsQuestion nodePropertiesQuestion = new RadioButtonsQuestion("nodeProperties", 
                                                                             nodePropertiesTitle, 
                                                                             isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_RC_NODE_PROPERTIES) : null,
                                                                             false,
                                                                             null, 
                                                                             new NotUndefinedValueValidator("Question '" + nodePropertiesTitle + "' not answered."), 
                                                                             false,
                                                                             choices);
      String reachedTitle = "Highlighting of source code reached during symbolic execution";
      RadioButtonsQuestion reachedQuestion = new RadioButtonsQuestion("reachedSourceCode", 
                                                                      reachedTitle, 
                                                                      isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_RC_REACHED) : null,
                                                                      false,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + reachedTitle + "' not answered."), 
                                                                      false,
                                                                      choices);
      String variablesTitle = "Shown variables of a node (view 'Variables')";
      RadioButtonsQuestion variablesQuestion = new RadioButtonsQuestion("variables", 
                                                                        variablesTitle, 
                                                                        isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_RC_VARIABLES) : null,
                                                                        false,
                                                                        null, 
                                                                        new NotUndefinedValueValidator("Question '" + variablesTitle + "' not answered."), 
                                                                        false,
                                                                        choices);
      SectionQuestion sedSection = new SectionQuestion("SED", "SED", false, setQuestion, nodePropertiesQuestion, reachedQuestion, variablesQuestion);
      // NO_TOOL vs SED
      String keyVsSedTitle = "I prefer to inspect source code";
      RadioButtonsQuestion keyVsSedQuestion = new RadioButtonsQuestion("toolPreference", 
                                                                       keyVsSedTitle, 
                                                                       true,
                                                                       null, 
                                                                       new NotUndefinedValueValidator("Question '" + keyVsSedTitle + "' not answered."), 
                                                                       false,
                                                                       new Choice("directly", "Directly"),
                                                                       new Choice("directly and using SED, both are equally good", "DirectlyAndSEDequal"),
                                                                       new Choice("directly and using SED, depending on the source code", "DirectlyAndSEDcodeBased"),
                                                                       new Choice("directly and using SED, both are equally bad and should be improved", "DirectlyAndSEDbad"),
                                                                       new Choice("using SED", "SED"));
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
                              sedSection,
                              keyVsSedSection,
                              feedbackSection);
   }
   
   
   
   

   
   private QuestionPage createValueSearchQuestionPage(String pageName, String title) {
      String method = "find(int[], int)";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("Search may not stop after an index was accepted by method accept", "SearchDoesNotStop"), 
                                                             new Choice("Search may not check all array elements even if no index was accepted by method accept", "NotAllConsidered"), 
                                                             new Choice("Not the first accepted index might be returned", "NotFirstFoundReturned"), 
                                                             new Choice("-1 might be returned instead of the accepted index", "MinusOneReturned"), 
                                                             new Choice("Accepted index might be returned instead of -1", "AcceptedIndexReturned"), 
                                                             new Choice("Value at accepted index might not be equal to the search criteria of method " + method, "WrongIndex", true), 
                                                             createThrownExceptionsQuestionChoice(description, true, false, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, false);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 20: return new ValueSearch().search(array)", "Line 20", true),
                                                               new Choice("Line 30: if (index < 0 || index >= array.length)", "Line 30", true),
                                                               new Choice("Line 31: return false", "Line 31"),
                                                               new Choice("Line 34: return array[index] == value", "Line 34", true));
      String returnValueTitle = "Which claims about the returned value of " + method + " are true?";
      CheckboxQuestion returnValue = new CheckboxQuestion("returnValue", 
                                                          returnValueTitle, 
                                                          description,
                                                          true,
                                                          null, 
                                                          new NotUndefinedValueValidator("Question '" + returnValueTitle + "' not answered."), 
                                                          true,
                                                          new Choice("An integer < -1 might be returned", "LessMinusOne"),
                                                          new Choice("-1 is returned if no index was accepted by method accept", "MinusOneNotFound", true),
                                                          new Choice("-1 might be returned even if an index was accepted by method accept", "MinusOneFound"),
                                                          new Choice("0 might be returned", "NullReturned", true),
                                                          new Choice("array.length - 1 might be returned", "LengthMinusOneReturned", true),
                                                          new Choice("array.length might be returned", "LengthReturned"),
                                                          new Choice("An integer within array bounds might be returned if no index was accepted by method accept", "IndexNotFoundReturned"),
                                                          new Choice("An integer within array bounds is returned if an index was accepted by method accept", "IndexFoundReturned", true));
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              new ReviewingCodeJavaProjectModifier("ValueSearch", 
                                                                   true,  
                                                                   null,
                                                                   new ProofFileFileDefinition[] {new ProofFileFileDefinition("data/reviewingCode/exampleValueSearch/proofs/find.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/find.proof", false, "ValueSearch", "find", new String[] {"[I", "I"})},
                                                                   new FileDefinition[] {new FileDefinition("data/reviewingCode/exampleValueSearch/src/AbstractSearch.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/AbstractSearch.java", true), 
                                                                                         new FileDefinition("data/reviewingCode/exampleValueSearch/srcWithMain/ValueSearch.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ValueSearch.java", true)},
                                                                   new FileDefinition("data/reviewingCode/exampleValueSearch/src/AbstractSearch.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/AbstractSearch.java", true),
                                                                   new FileDefinition("data/reviewingCode/exampleValueSearch/src/ValueSearch.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ValueSearch.java", true)),
                              createGeneralClassDescriptionQuestion("ValueSearch"),
                              implementedAsDocumented,
                              executedQuestion,
                              createValueSearchLocationQuestion(description, method),
                              returnValue,
                              createSEDUsedQuestion(),
                              createCodeExecutedQuestion());
   }

   private CheckboxQuestion createValueSearchLocationQuestion(String description, String method) {
      String title = createChangedLocationTitle("ValueSearch", method);
      return new CheckboxQuestion("changedLocations", 
                                  title, 
                                  description,
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  ASK_FOR_CHANGED_LOCATIONS,
                                  new Choice("None", "None"),
                                  new Choice("value", "value"),
                                  new Choice("something else", "SomethingElse", createElseLocationSubQuestion(description)));
   }

   
   
   
   

   

   private QuestionPage createBankUtilQuestionPage(String pageName, String title) {
      String method = "computeInsuranceRate(int)";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("Wrong value returned in case age < 18", "WrongLess18", createBankUtilReturnedValue(description, false)), 
                                                             new Choice("Wrong value returned in case age >= 18 and age < 19", "WrongLess19", createBankUtilReturnedValue(description, false)), 
                                                             new Choice("Wrong value returned in case age >= 19 and age < 21", "WrongLess21", createBankUtilReturnedValue(description, false)), 
                                                             new Choice("Wrong value returned in case age >= 21 and age < 35", "WrongLess35", createBankUtilReturnedValue(description, false)), 
                                                             new Choice("Wrong value returned in case age >= 35", "WrongGreaterOrEqual35", true, createBankUtilReturnedValue(description, true)), 
                                                             new Choice("No value might be returned", "NoReturn"), 
                                                             createThrownExceptionsQuestionChoice(description, false, false, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, false);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 18: int[] ageLimits = {18, 19, 21, 35, 65}", "Line 18", true),
                                                               new Choice("Line 19: long[] insuranceRates = {200, 250, 300, 450, 575}", "Line 19", true),
                                                               new Choice("Line 20: int ageLevel = 0", "Line 20", true),
                                                               new Choice("Line 21: long insuranceRate = 570", "Line 21", true),
                                                               new Choice("Line 22: while (ageLevel < ageLimits.length - 1)", "Line 22", true),
                                                               new Choice("Line 23: if (age < ageLimits[ageLevel])", "Line 23", true),
                                                               new Choice("Line 24: return insuranceRates[ageLevel]", "Line 24", true),
                                                               new Choice("Line 26: ageLevel++", "Line 26", true),
                                                               new Choice("Line 28: return insuranceRate", "Line 28", true));
      String returnValueTitle = "Which claims about the returned value of " + method + " are true?";
      CheckboxQuestion returnValue = new CheckboxQuestion("returnValue", 
                                                          returnValueTitle, 
                                                          description,
                                                          true,
                                                          null, 
                                                          new NotUndefinedValueValidator("Question '" + returnValueTitle + "' not answered."), 
                                                          true,
                                                          new Choice("A negative integer might be returned", "Negative"),
                                                          new Choice("0 might be returned", "Null"),
                                                          new Choice("Length of ageLimits might be returned", "AgeLimitsLength"),
                                                          new Choice("An integer contained in ageLimits might be returned", "ContainedInAgeLimits"),
                                                          new Choice("An integer not contained in ageLimits might be returned", "NotContainedInAgeLimits", true),
                                                          new Choice("Length of insuranceRates might be returned", "InsuranceRatesLength"),
                                                          new Choice("An integer contained in insuranceRates might be returned", "ContainedInInsuranceRates", true),
                                                          new Choice("An integer not contained in insuranceRates might be returned", "NotContainedInInsuranceRates", true),
                                                          new Choice("A positive integer might be returned", "Positive", true));
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              new ReviewingCodeJavaProjectModifier("BankUtil", 
                                                                   true,  
                                                                   null,
                                                                   new ProofFileFileDefinition[] {new ProofFileFileDefinition("data/reviewingCode/exampleInsuranceRate/proofs/computeInsuranceRate.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/computeInsuranceRate.proof", false, "BankUtil", "computeInsuranceRate", new String[] {"I"})},
                                                                   new FileDefinition[] {new FileDefinition("data/reviewingCode/exampleInsuranceRate/srcWithMain/BankUtil.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/BankUtil.java", true)},
                                                                   new FileDefinition("data/reviewingCode/exampleInsuranceRate/src/BankUtil.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/BankUtil.java", true)),
                              createGeneralClassDescriptionQuestion("BankUtil"),
                              implementedAsDocumented,
                              executedQuestion,
                              returnValue,
                              createSEDUsedQuestion(),
                              createCodeExecutedQuestion());
   }

   private CheckboxQuestion createBankUtilReturnedValue(String description, boolean expectedSelected) {
      String returnedValueTitle = "Which value is returned?";
      return new CheckboxQuestion("methodProblems", 
                                  returnedValueTitle, 
                                  description,
                                  true, 
                                  null, 
                                  createNotUndefinedValueValidator(returnedValueTitle), 
                                  true,
                                  new Choice("-1", "-1"), 
                                  new Choice("0", "0"), 
                                  new Choice("18", "18"), 
                                  new Choice("19", "19"), 
                                  new Choice("21", "21"), 
                                  new Choice("35", "35"), 
                                  new Choice("65", "65"), 
                                  new Choice("200", "200"), 
                                  new Choice("250", "250"), 
                                  new Choice("300", "300"), 
                                  new Choice("450", "450"), 
                                  new Choice("570", "570", expectedSelected), 
                                  new Choice("575", "575"), 
                                  createElseRetrunedChoice(description));

   }

   
   
   
   

   
   private QuestionPage createMathUtilQuestionPage(String pageName, String title) {
      String method = "median(int[], int, int)";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("Middle value is returned instead of the average", "MiddleInsteadOfAverage"), 
                                                             new Choice("Average is returned instead of the middle value", "AverageInsteadOfMiddle"), 
                                                             new Choice("Average is computed wrongly", "WrongAverage"), 
                                                             new Choice("A documented exception might be thrown instead of returning median value", "ExceptionThrown"), 
                                                             new Choice("Media value might be returned instead of throwing a documented exception", "ValueReturned"), 
                                                             createThrownExceptionsQuestionChoice(description, false, false, false, false, true, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, false);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 24: if (array == null)", "Line 22", true),
                                                               new Choice("Line 25: throw new IllegalArgumentException(\"Array is null.\")", "Line 23", true),
                                                               new Choice("Line 27: if (start < 0 || start >= array.length)", "Line 25", true),
                                                               new Choice("Line 28: throw new IllegalArgumentException(\"Start is not within the array bounds.\")", "Line 26", true),
                                                               new Choice("Line 30: if (end < 0 || end >= array.length)", "Line 28", true),
                                                               new Choice("Line 31: throw new IllegalArgumentException(\"Start is not within the array bounds.\")", "Line 29", true),
                                                               new Choice("Line 34: int middle = (start + end) / 2", "Line 32", true),
                                                               new Choice("Line 35: if ((start + end) % 2 == 0)", "Line 33", true),
                                                               new Choice("Line 36: return array[middle]", "Line 34", true),
                                                               new Choice("Line 39: return (array[middle] + array[middle + 1]) / 2", "Line 37", true));
      String returnValueTitle = "Which claims about the returned value of " + method + " are true?";
      CheckboxQuestion returnValue = new CheckboxQuestion("returnValue", 
                                                          returnValueTitle, 
                                                          description,
                                                          true,
                                                          null, 
                                                          new NotUndefinedValueValidator("Question '" + returnValueTitle + "' not answered."), 
                                                          true,
                                                          new Choice("A negative integer might be returned", "Negative", true),
                                                          new Choice("0 might be returned", "Null", true),
                                                          new Choice("A positive integer might be returned", "Positive", true),
                                                          new Choice("An integer contained in array might be returned", "InArray", true),
                                                          new Choice("An integer not contained in array might be returned", "NotInArray", true));
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              new ReviewingCodeJavaProjectModifier("MathUtil", 
                                                                   true,  
                                                                   null,
                                                                   new ProofFileFileDefinition[] {new ProofFileFileDefinition("data/reviewingCode/exampleMedian/proofs/median.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/median.proof", false, "MathUtil", "median", new String[] {"[I", "I", "I"})},
                                                                   new FileDefinition[] {new FileDefinition("data/reviewingCode/exampleMedian/srcWithMain/MathUtil.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MathUtil.java", true)},
                                                                   new FileDefinition("data/reviewingCode/exampleMedian/src/MathUtil.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/MathUtil.java", true)),
                              createGeneralClassDescriptionQuestion("MathUtil"),
                              implementedAsDocumented,
                              executedQuestion,
                              returnValue,
                              createSEDUsedQuestion(),
                              createCodeExecutedQuestion());
   }

   
   
   
   

   
   private QuestionPage createIntegerUtilQuestionPage(String pageName, String title) {
      String method = "middle(int, int, int)";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("x returned instead of y", "xInsteadOfy"), 
                                                             new Choice("x returned instead of z", "xInsteadOfz"), 
                                                             new Choice("y returned instead of x", "yInsteadOfx", true), 
                                                             new Choice("y returned instead of z", "yInsteadOfz"), 
                                                             new Choice("z returned instead of x", "zInsteadOfx"), 
                                                             new Choice("z returned instead of y", "zInsteadOfy"), 
                                                             new Choice("No value might be returned", "NoReturn"), 
                                                             createThrownExceptionsQuestionChoice(description, false, false, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, false);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 13: if (y < z)", "Line 13", true),
                                                               new Choice("Line 14: if (x < y)", "Line 14", true),
                                                               new Choice("Line 15: return y", "Line 15", true),
                                                               new Choice("Line 18: if (x < z)", "Line 18", true),
                                                               new Choice("Line 19: return y", "Line 19", true),
                                                               new Choice("Line 24: if (x > y)", "Line 24", true),
                                                               new Choice("Line 25: return y", "Line 25", true),
                                                               new Choice("Line 28: if (x > z)", "Line 28", true),
                                                               new Choice("Line 29: return x", "Line 29", true),
                                                               new Choice("Line 33: return z", "Line 33", true));
      String returnValueTitle = "Which claims about the returned value of " + method + " are true?";
      CheckboxQuestion returnValue = new CheckboxQuestion("returnValue", 
                                                          returnValueTitle, 
                                                          description,
                                                          true,
                                                          null, 
                                                          new NotUndefinedValueValidator("Question '" + returnValueTitle + "' not answered."), 
                                                          true,
                                                          new Choice("A negative integer might be returned", "Negative", true),
                                                          new Choice("0 might be returned", "Null", true),
                                                          new Choice("A positive integer might be returned", "Positive", true),
                                                          new Choice("x might be returned", "x", true),
                                                          new Choice("y might be returned", "y", true),
                                                          new Choice("z might be returned", "z", true),
                                                          new Choice("An integer which is not x, y or z might be returned", "notXYZ"));
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              new ReviewingCodeJavaProjectModifier("IntegerUtil", 
                                                                   true,  
                                                                   null,
                                                                   new ProofFileFileDefinition[] {new ProofFileFileDefinition("data/reviewingCode/exampleMiddle/proofs/middle.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/middle.proof", false, "IntegerUtil", "middle", new String[] {"I", "I", "I"})},
                                                                   new FileDefinition[] {new FileDefinition("data/reviewingCode/exampleMiddle/srcWithMain/IntegerUtil.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/IntegerUtil.java", true)},
                                                                   new FileDefinition("data/reviewingCode/exampleMiddle/src/IntegerUtil.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/IntegerUtil.java", true)),
                              createGeneralClassDescriptionQuestion("IntegerUtil"),
                              implementedAsDocumented,
                              executedQuestion,
                              returnValue,
                              createSEDUsedQuestion(),
                              createCodeExecutedQuestion());
   }
   
   
   
   
   
   
   
   
   
   
   private QuestionPage createObservableArrayQuestionPage(String pageName, String title) {
      TabbedQuestion tabbedQuestion = new TabbedQuestion("methods", 
                                                         createObservableArrayArrayTab(),
                                                         createSetTab(),
                                                         createSetArrayListenersTab());
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              false,
                              false,
                              true,
                              new ReviewingCodeJavaProjectModifier("ObservableArray", 
                                                                   true, 
                                                                   null,
                                                                   new ProofFileFileDefinition[] {new ProofFileFileDefinition("data/reviewingCode/exampleObservableArray/proofs/ObservableArray.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ObservableArray.proof", false, "ObservableArray", "ObservableArray", new String[] {"[QObject;"}),
                                                                                                  new ProofFileFileDefinition("data/reviewingCode/exampleObservableArray/proofs/set.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/set.proof", false, "ObservableArray", "set", new String[] {"I", "QObject;"}),
                                                                                                  new ProofFileFileDefinition("data/reviewingCode/exampleObservableArray/proofs/setArrayListeners.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/setArrayListeners.proof", false, "ObservableArray", "setArrayListeners", new String[] {"[QArrayListener;"})},
                                                                   new FileDefinition[] {new FileDefinition("data/reviewingCode/exampleObservableArray/src/ArrayEvent.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ArrayEvent.java", true), 
                                                                                         new FileDefinition("data/reviewingCode/exampleObservableArray/src/ArrayListener.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ArrayListener.java", true),
                                                                                         new FileDefinition("data/reviewingCode/exampleObservableArray/srcWithMain/ObservableArray.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ObservableArray.java", true)},
                                                                   new FileDefinition("data/reviewingCode/exampleObservableArray/src/ArrayEvent.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ArrayEvent.java", true),
                                                                   new FileDefinition("data/reviewingCode/exampleObservableArray/src/ArrayListener.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ArrayListener.java", true),
                                                                   new FileDefinition("data/reviewingCode/exampleObservableArray/src/ObservableArray.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/ObservableArray.java", true)),
                              createGeneralClassDescriptionQuestion("ObservableArray"),
                              tabbedQuestion);
   }
   
   private TabQuestion createObservableArrayArrayTab() {
      String method = "ObservableArray(Object[])";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("Future calls of set(int, Object) will not modify the given array", "ArrayNotModified"), 
                                                             new Choice("ObservableArray might be created instead of throwing a documented exception", "ExceptionMissing"), 
                                                             new Choice("A document exception might be thrown instead of creating an ObservableArray", "ExceptionThrown"), 
                                                             createThrownExceptionsQuestionChoice(description, false, false, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, true);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 34: if (array == null)", "Line 30", true),
                                                               new Choice("Line 35: throw new IllegalArgumentException(\"Array is null.\")", "Line 31", true),
                                                               new Choice("Line 37: this.array = array", "Line 33", true),
                                                               new Choice("Line 38: this.arrayListeners = null", "Line 34", true));
      return new TabQuestion("ObservableArray", 
                             method, 
                             false, 
                             implementedAsDocumented,
                             createObservableArrayClassInvariantQuestion(description, method, true),
                             executedQuestion,
                             createObservableArrayLocationQuestion(description, method, true, true, false, false),
                             createSEDUsedQuestion(),
                             createCodeExecutedQuestion());
   }
   
   private TabQuestion createSetTab() {
      String method = "set(int, Object)";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("array[index] is not assigned to element", "ArrayNotUpdated"), 
                                                             new Choice("Not all ArrayListener of arrayListeners at call time might be informed about the change", "ArrayListenerNotInformed", true), 
                                                             new Choice("The ArrayEvent does not contains all details about the modification.", "ArrayEventDoesNotHaveDetails"), 
                                                             createThrownExceptionsQuestionChoice(description, true, false, false, false, true, true),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, false);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 51: array[index] = element", "Line 47", true),
                                                               new Choice("Line 52: fireElementChanged(new ArrayEvent(this, index, element))", "Line 48", true),
                                                               new Choice("Line 61: if (arrayListeners != null)", "Line 57", true),
                                                               new Choice("Line 66: int i = 0", "Line 62 initial", true),
                                                               new Choice("Line 66: i < arrayListeners.length", "Line 62 guard", true),
                                                               new Choice("Line 66: i++", "Line 62 increment", true),
                                                               new Choice("Line 67: if (arrayListeners[i] != null)", "Line 63", true),
                                                               new Choice("Line 68: arrayListeners[i].elementChanged(e)", "Line 64", true));
      return new TabQuestion("set", 
                             method, 
                             false, 
                             implementedAsDocumented,
                             createObservableArrayClassInvariantQuestion(description, method, false),
                             executedQuestion,
                             createObservableArrayLocationQuestion(description, method, false, true, true, true),
                             createSEDUsedQuestion(),
                             createCodeExecutedQuestion());
   }
   
   private TabQuestion createSetArrayListenersTab() {
      String method = "setArrayListeners(ArrayListener[])";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("ArrayListener are not replaced by the new one", "ArrayListenerNotReplaced"), 
                                                             createThrownExceptionsQuestionChoice(description, false, false, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, false);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 79: this.arrayListeners = arrayListeners", "Line 75", true));
      return new TabQuestion("setArrayListeners", 
                             method, 
                             false, 
                             implementedAsDocumented,
                             createObservableArrayClassInvariantQuestion(description, method, false),
                             executedQuestion,
                             createObservableArrayLocationQuestion(description, method, false, true, false, false),
                             createSEDUsedQuestion(),
                             createCodeExecutedQuestion());
   }
   
   private RadioButtonsQuestion createObservableArrayClassInvariantQuestion(String description, String method, boolean constructor) {
      String problemsTitle = "What is wrong?";
      CheckboxQuestion problems = new CheckboxQuestion("classInvariantProblems", 
                                                       problemsTitle, 
                                                       description,
                                                       true, 
                                                       null, 
                                                       createNotUndefinedValueValidator(problemsTitle), 
                                                       true,
                                                       new Choice("array might be null", "ArrayNull"), 
//                                                       new Choice("array might be not null", "ArrayNotNull"), 
//                                                       new Choice("array might have length 0", "ArrayLengthZero"), 
                                                       new Choice("array might be empty", "ArrayEmpty"), 
//                                                       new Choice("array might be not empty", "ArrayNotEmpty"), 
                                                       new Choice("array might contain null as element", "ArrayContainsNull"), 
//                                                       new Choice("array might contain an Object as element", "ArrayContainsObject"), 
                                                       new Choice("arrayListeners might be null", "ArrayListenersNull"), 
//                                                       new Choice("arrayListeners might be not null", "ArrayListenersNotNull"), 
//                                                       new Choice("arrayListeners might have length 0", "ArrayListenersLengthZero"), 
                                                       new Choice("arrayListeners might be empty", "ArrayListenersEmpty"), 
//                                                       new Choice("arrayListeners might be not empty", "ArrayListenersNotEmpty"), 
                                                       new Choice("arrayListeners might contain null as element", "ArrayListenersContainsNull"), 
//                                                       new Choice("arrayListeners might contain an Object as element", "ArrayarrayListenersContainsObject"), 
                                                       createElseWrongChoice(description));
      String title = constructor ?
                     "Is the class invariant established by " + method + " in case of normal termination?" :
                     "Is the class invariant preserved by " + method + "?";
      return new RadioButtonsQuestion("classInvariant", 
                                      title, 
                                      description,
                                      true, 
                                      null, 
                                      createNotUndefinedValueValidator(title), 
                                      true,
                                      new Choice("Yes", "Yes", true), 
                                      new Choice("No", "No", problems));
   }

   private CheckboxQuestion createObservableArrayLocationQuestion(String description, 
                                                                  String method, 
                                                                  boolean expectedArray, 
                                                                  boolean expectedArrayListeners, 
                                                                  boolean expectedAllArrayIndices,
                                                                  boolean expectedAllArrayListenerIndices) {
      String title = createChangedLocationTitle("ObservableArray", method);
      return new CheckboxQuestion("changedLocations", 
                                  title, 
                                  description,
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  ASK_FOR_CHANGED_LOCATIONS,
                                  new Choice("None", "None"),
                                  new Choice("array", "array", expectedArray),
                                  new Choice("array[index]", "array[index]", expectedAllArrayIndices),
                                  new Choice("array[*]", "array[*]", expectedAllArrayIndices),
                                  new Choice("array.length", "array.length"),
                                  new Choice("arrayListeners", "arrayListeners", expectedArrayListeners),
                                  new Choice("arrayListeners[*]", "arrayListeners[*]", expectedAllArrayListenerIndices),
                                  new Choice("arrayListeners.length", "arrayListeners.length"),
                                  new Choice("something else", "SomethingElse", createElseExceptionSubQuestion(description)));
   }
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   

   private QuestionPage createStackQuestionPage(String pageName, String title) {
      TabbedQuestion tabbedQuestion = new TabbedQuestion("methods", 
                                                         createStackIntTab(),
                                                         createStackStackTab(),
                                                         createPushTab(),
                                                         createPopTab());
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              false,
                              false,
                              true,
                              new ReviewingCodeJavaProjectModifier("Stack", 
                                                                   true, 
                                                                   new FileDefinition("data/reviewingCode/exampleStack/boot", "stubs", false),
                                                                   new ProofFileFileDefinition[] {new ProofFileFileDefinition("data/reviewingCode/exampleStack/proofs/Stack_int.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Stack_int.proof", false, "Stack", "Stack", new String[] {"I"}),
                                                                                                  new ProofFileFileDefinition("data/reviewingCode/exampleStack/proofs/Stack_Stack.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Stack_Stack.proof", false, "Stack", "Stack", new String[] {"QStack;"}),
                                                                                                  new ProofFileFileDefinition("data/reviewingCode/exampleStack/proofs/push.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/push.proof", false, "Stack", "push", new String[] {"QObject;"}),
                                                                                                  new ProofFileFileDefinition("data/reviewingCode/exampleStack/proofs/pop.proof", JavaProjectModifier.SOURCE_FOLDER_NAME + "/pop.proof", false, "Stack", "pop", new String[] {})},
                                                                   new FileDefinition[] {new FileDefinition("data/reviewingCode/exampleStack/srcWithMain/Stack.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Stack.java", true)},
                                                                   new FileDefinition("data/reviewingCode/exampleStack/src/Stack.java", JavaProjectModifier.SOURCE_FOLDER_NAME + "/Stack.java", true)),
                              createGeneralClassDescriptionQuestion("Stack"),
                              tabbedQuestion);
   }
   
   private TabQuestion createStackIntTab() {
      String method = "Stack(int)";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
//                                                             new Choice("The created stack is empty", "StackEmpty"), 
                                                             new Choice("The created stack is not empty", "StackNotEmpty"), 
//                                                             new Choice("The created stack can be filled up to maximal size", "StackSizeMaximal"),
                                                             new Choice("The created stack can not be filled up to maximal size", "StackSizeNotMaximal"),
                                                             createThrownExceptionsQuestionChoice(description, false, true, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, true);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 33: elements = new Object[maximalSize]", "Line 33", true),
                                                               new Choice("Line 34: size = 0", "Line 34", true));
      return new TabQuestion("Stack_int", 
                             method, 
                             false, 
                             implementedAsDocumented,
                             createStackClassInvariantQuestion(description, method, true, false),
                             executedQuestion,
                             createStackLocationQuestion(description, method, true, true, false),
                             createSEDUsedQuestion(),
                             createCodeExecutedQuestion());
   }
   
   private TabQuestion createStackStackTab() {
      String method = "Stack(Stack)";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("The created stack provides different content as the existing one", "DifferentContent"),
                                                             new Choice("The created stack has different size as the existing one", "DifferentSize"),
                                                             new Choice("The created stack has same elements array as the existing one", "SameElements", true),
                                                             createThrownExceptionsQuestionChoice(description, true, false, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, true);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 44: this.elements = existingStack.elements", "Line 43", true),
                                                               new Choice("Line 45: this.size = existingStack.size", "Line 44", true));
      return new TabQuestion("Stack_Stack", 
                             method, 
                             false, 
                             implementedAsDocumented,
                             createStackClassInvariantQuestion(description, method, true, false),
                             executedQuestion,
                             createStackLocationQuestion(description, method, true, true, false),
                             createSEDUsedQuestion(),
                             createCodeExecutedQuestion());
   }
   
   private TabQuestion createPushTab() {
      String method = "push(Object)";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("size is not updated", "SizeNotUpdated"), 
//                                                             new Choice("elements is replaced by a different array", "ElementsChanged"), 
                                                             new Choice("elements is not updated", "ElementsNotUpdated"), 
                                                             new Choice("e is stored at wrong index in array elements", "StoredAtWrongIndex"), 
                                                             new Choice("A documented exception might be thrown instead of updating the stack", "ExceptionThrown"), 
                                                             new Choice("Stack might be updated instead of throwing a documented exception", "ExceptionNOtThrown"), 
//                                                             new Choice("Executing pop after push would not return the added element.", "PushPopBroken"), 
                                                             createThrownExceptionsQuestionChoice(description, false, false, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, false);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 54: if (size < elements.length)", "Line 53", true),
                                                               new Choice("Line 55: elements[size++] = e", "Line 54", true),
                                                               new Choice("Line 58: throw new IllegalStateException(\"Stack is full.\")", "Line 57", true));
      return new TabQuestion("push(Object)", 
                             method, 
                             false, 
                             implementedAsDocumented,
                             createStackClassInvariantQuestion(description, method, false, false),
                             executedQuestion,
                             createStackLocationQuestion(description, method, false, true, true),
                             createSEDUsedQuestion(),
                             createCodeExecutedQuestion());
   }
   
   private TabQuestion createPopTab() {
      String method = "pop()";
      String description = method + " related question.";
      String methodProblemsTitle = createWhatsWrongTitle();
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("size is not updated", "SizeNotUpdated"), 
                                                             new Choice("elements is not updated", "ElementsNotUpdated", true), 
                                                             new Choice("Element at wrong index in array elements is returned", "WrongIndexReturned"), 
                                                             new Choice("A documented exception might be thrown instead of returning the top element", "ExceptionThrown"), 
                                                             new Choice("Top element might be returned instead of throwing a documented exception", "ExceptionNOtThrown"), 
//                                                             new Choice("Executing pop twice would return the same element twice.", "PopPopBroken"), 
                                                             createThrownExceptionsQuestionChoice(description, false, false, false, false, false, false),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = createImplementedAsDocumentedTitle(method, false);
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String returnValueTitle = "Which claims about the returned value of " + method + " are true?";
      CheckboxQuestion returnValue = new CheckboxQuestion("returnValue", 
                                                          returnValueTitle, 
                                                          description,
                                                          true,
                                                          null, 
                                                          new NotUndefinedValueValidator("Question '" + returnValueTitle + "' not answered."), 
                                                          true,
                                                          new Choice("null might be returned", "NullReturned", true),
                                                          new Choice("An object might be returned", "ObjectReturned", true),
                                                          new Choice("Element at index size is returned", "ElementAtSizeReturned"),
                                                          new Choice("Element at index size - 1 is returned", "ElementAtSizePlusOneReturned", true));
      String executedTitle = createExecutedQuestion(method);
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 68: if (size >= 1)", "Line 67", true),
                                                               new Choice("Line 69: return elements[--size]", "Line 68", true),
                                                               new Choice("Line 72: throw new IllegalStateException(\"Stack is empty.\")", "Line 71", true));
      return new TabQuestion("pop()", 
                             method, 
                             false, 
                             implementedAsDocumented,
                             createStackClassInvariantQuestion(description, method, false, true),
                             executedQuestion,
                             createStackLocationQuestion(description, method, false, true, false),
                             returnValue,
                             createSEDUsedQuestion(),
                             createCodeExecutedQuestion());
   }
   
   private RadioButtonsQuestion createSEDUsedQuestion() {
      String title = "Does the symbolic execution tree help to answer the questions?";
      return new RadioButtonsQuestion("setConsidered", 
                                      title, 
                                      (String) null,
                                      true, 
                                      null, 
                                      createNotUndefinedValueValidator(title), 
                                      false,
                                      new Tool[] {getTool(SED_TOOL_NAME)},
                                      new Choice("Yes, Very helpful", "YesVeryHelpful"), 
                                      new Choice("Yes, Helpful", "YesHelpful"), 
                                      new Choice("Yes, Little helpful", "YesLittleHelpful"), 
                                      new Choice("No, Not helpful", "NoNotHelpful"),
                                      new Choice("Not considered", "NotConsidered"));
   }
   
   private RadioButtonsQuestion createCodeExecutedQuestion() {
      String helpfulTitle = "Does executing/debugging the source code help to answer the questions?";
      RadioButtonsQuestion helpfulQuestion = new RadioButtonsQuestion("executionHelpful", 
                                                                      helpfulTitle, 
                                                                      (String) null,
                                                                      true, 
                                                                      null, 
                                                                      createNotUndefinedValueValidator(helpfulTitle), 
                                                                      false,
                                                                      new Tool[] {getTool(NO_TOOL_NAME)},
                                                                      new Choice("Yes, Very helpful", "YesVeryHelpful"), 
                                                                      new Choice("Yes, Helpful", "YesHelpful"), 
                                                                      new Choice("Yes, Little helpful", "YesLittleHelpful"), 
                                                                      new Choice("No, Not helpful", "NoNotHelpful"));
      String writtenCodetitle = "Which code has been written?";
      TextQuestion writtenCodeQuestion = new TextQuestion("writtenCode", 
                                                          writtenCodetitle, 
                                                          "(Only final code version if still available.)", 
                                                          null, 
                                                          null, 
                                                          false,
                                                          new Tool[] {getTool(NO_TOOL_NAME)},
                                                          400, 
                                                          200);
      String title = "Have you executed/debugged the source code to answer the questions?";
      return new RadioButtonsQuestion("codeExecuted", 
                                      title, 
                                      (String) null,
                                      true, 
                                      null, 
                                      createNotUndefinedValueValidator(title), 
                                      false,
                                      new Tool[] {getTool(NO_TOOL_NAME)},
                                      new Choice("Yes", "Yes", helpfulQuestion, writtenCodeQuestion), 
                                      new Choice("No", "No"));
   }

   private Choice createElseRetrunedChoice(String description) {
      return new Choice("Something else is returned", "SomethingElse", createElseReturnedSubQuestion(description));
   }

   private TextQuestion createElseReturnedSubQuestion(String description) {
      String title = "What is returned?";
      return new TextQuestion("whatsReturned", title, description, null, new NotUndefinedValueValidator("Question '" + title + "' not answered."), false, 400, -1);
   }

   private Choice createElseWrongChoice(String description) {
      return new Choice("Something else is wrong", "SomethingElse", createElseWrongSubQuestion(description));
   }

   private TextQuestion createElseWrongSubQuestion(String description) {
      String title = "What else is wrong?";
      return new TextQuestion("whatsWrong", title, description, null, new NotUndefinedValueValidator("Question '" + title + "' not answered."), false, 400, -1);
   }
   
   private RadioButtonsQuestion createStackClassInvariantQuestion(String description, 
                                                                  String method,
                                                                  boolean constructor, 
                                                                  boolean expectedMemoryLeak) {
      String problemsTitle = "What is wrong?";
      CheckboxQuestion problems = new CheckboxQuestion("classInvariantProblems", 
                                                       problemsTitle, 
                                                       description,
                                                       true, 
                                                       null, 
                                                       createNotUndefinedValueValidator(problemsTitle), 
                                                       true,
                                                       new Choice("elements might be null.", "ElementsNull"), 
//                                                       new Choice("elements might be non null.", "ElementsNonNull"), 
//                                                       new Choice("elements might be of type Object[].", "ElementsTypeObjectArray"), 
                                                       new Choice("elements might be not of type Object[].", "ElementsTypeNotObjectArray"), 
                                                       new Choice("Element at index < size might be null", "ContainedElementNull"), 
                                                       new Choice("Element at index < size might be non null", "ContainedElementNonNull"), 
                                                       new Choice("Element at index >= size might be null", "NotContainedElementNull"), 
                                                       new Choice("Element at index >= size might be non null", "NotContainedElementNonNull", expectedMemoryLeak), 
                                                       new Choice("size might be < 0", "NegativeSize"), 
//                                                       new Choice("size might be < elements.length", "SizeLessArrayLength"), 
//                                                       new Choice("size might be = elements.length", "SizeEqualArrayLength"), 
                                                       new Choice("size might be > elements.length", "SizeGreaterArrayLength"), 
                                                       createElseWrongChoice(description));
      String title = constructor ?
                     "Is the class invariant established by " + method + " in case of normal termination?" :
                     "Is the class invariant preserved by " + method + "?";
      return new RadioButtonsQuestion("classInvariant", 
                                      title, 
                                      description,
                                      true, 
                                      null, 
                                      createNotUndefinedValueValidator(title), 
                                      true,
                                      new Choice("Yes", "Yes", !expectedMemoryLeak), 
                                      new Choice("No", "No", expectedMemoryLeak, problems));
   }

   private CheckboxQuestion createStackLocationQuestion(String description, String method, boolean expectedElements, boolean expectedSize, boolean expectedElementAtPlus1) {
      String title = createChangedLocationTitle("Stack", method);
      return new CheckboxQuestion("changedLocations", 
                                  title, 
                                  description,
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  ASK_FOR_CHANGED_LOCATIONS,
                                  new Choice("None", "None"),
                                  new Choice("elements", "elements", expectedElements),
                                  new Choice("elements[size - 1]", "elements[size - 1]"),
                                  new Choice("elements[size]", "elements[size]"),
                                  new Choice("elements[size + 1]", "elements[size + 1]", expectedElementAtPlus1),
                                  new Choice("elements[*]", "elements[*]"),
                                  new Choice("elements.length", "elements.length"),
                                  new Choice("size", "size", expectedSize),
                                  new Choice("something else", "SomethingElse", createElseLocationSubQuestion(description)));
   }
   
   private TextQuestion createElseLocationSubQuestion(String description) {
      String locationTitle = "Which additional location(s) can be changed?";
      return new TextQuestion("elseLocation", locationTitle, description, null, new NotUndefinedValueValidator("Question '" + locationTitle + "' not answered."), false, 400, -1);
   }

   private Choice createThrownExceptionsQuestionChoice(String description, 
                                                       boolean expectedNPE, 
                                                       boolean expectedNASE, 
                                                       boolean expectedISE, 
                                                       boolean expectedIAE, 
                                                       boolean expectedAIOOBE, 
                                                       boolean expectedASE) {
      return new Choice("A not documented exception might be thrown", 
                        "unexpectedException", 
                        expectedNPE || expectedNASE || expectedISE || expectedIAE || expectedAIOOBE || expectedASE,
                        createThrownExceptionsSubQuestion(description, expectedNPE, expectedNASE, expectedISE, expectedIAE, expectedAIOOBE, expectedASE));
   }

   private CheckboxQuestion createThrownExceptionsSubQuestion(String description, boolean expectedNPE, boolean expectedNASE, boolean expectedISE, boolean expectedIAE, boolean expectedAIOOBE, boolean expectedASE) {
      String thrownExceptionTitle = "Which not documented exception(s) might be thrown?";
      CheckboxQuestion thrownExceptionQuestion = new CheckboxQuestion("whichExceptionsMightBeThrown", 
                                                                      thrownExceptionTitle, 
                                                                      description,
                                                                      true,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + thrownExceptionTitle + "' not answered."), 
                                                                      true,
                                                                      new Choice("java.lang.NullPointerException", "java.lang.NullPointerException", expectedNPE),
                                                                      new Choice("java.lang.ArithmeticException", "java.lang.ArithmeticException"),
                                                                      new Choice("java.lang.ArrayIndexOutOfBoundsException", "java.lang.ArrayIndexOutOfBoundsException", expectedAIOOBE),
                                                                      new Choice("java.lang.ArrayStoreException", "java.lang.ArrayStoreException", expectedASE),
                                                                      new Choice("java.lang.NegativeArraySizeException", "java.lang.NegativeArraySizeException", expectedNASE),
                                                                      new Choice("java.lang.IllegalArgumentException", "java.lang.IllegalArgumentException", expectedIAE),
                                                                      new Choice("java.lang.IllegalStateException", "java.lang.IllegalStateException", expectedISE),
                                                                      new Choice("something else", "SomethingElse", createElseExceptionSubQuestion(description)));
      return thrownExceptionQuestion;
   }

   private TextQuestion createElseExceptionSubQuestion(String description) {
      String exceptionTitle = "Which exception is thrown?";
      return new TextQuestion("thrownException", exceptionTitle, description, null, new NotUndefinedValueValidator("Question '" + exceptionTitle + "' not answered."), false, 400, -1);
   }
   
   private IValueValidator createNotUndefinedValueValidator(String questionTitle) {
      return new NotUndefinedValueValidator("Question '" + questionTitle + "' not answered.");
   }
   
   private LabelQuestion createGeneralClassDescriptionQuestion(String className) {
      return new LabelQuestion("generalDescription", 
                               "Please inspect the current source code of class '" + className + "' carefully and answer the following questions about it as best as possible.",
                               Collections.singletonMap(getTool(SED_TOOL_NAME), "Please inspect the the current symbolic execution tree and the source code of class '" + className + "' carefully and answer the following questions about it as best as possible."));
   }

   protected String createQuestionPageMessage() {
      return "Please answer the questions to the best of your knowledge.";
   }
   
   protected String createExecutedQuestion(String startMethod) {
      return "Which statement(s) can be executed starting at " + startMethod + "?";
   }
   
   private String createWhatsWrongTitle() {
      return "Which is the observed wrong behavior?";
   }
   
   private String createChangedLocationTitle(String className, String method) {
      return "Which locations of class '" + className + "' might be assigned during execution of " + method + "? (Expressions are evaluated in the pre state before method call.)";
   }
   
   private String createImplementedAsDocumentedTitle(String method, boolean constructor) {
      if (constructor) {
         return "Does the constructor implementation of " + method + " always behaves as specified by its JavaDoc comment?";
      }
      else {
         return "Does the method implementation of " + method + "  always behaves as specified by its JavaDoc comment?";
      }
   }

   
   public RandomForm getEvaluationForm() {
      return (RandomForm) getForm(EVALUATION_FORM_NAME);
   }
}
