package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;
import java.util.List;

import org.key_project.sed.key.evaluation.model.util.EvaluationModelImages;
import org.key_project.sed.key.evaluation.model.validation.IValueValidator;
import org.key_project.sed.key.evaluation.model.validation.NotUndefinedValueValidator;
import org.key_project.util.java.CollectionUtil;

public class ReviewingCodeEvaluation extends AbstractEvaluation {
   /**
    * The only instance of this class.
    */
   public static final ReviewingCodeEvaluation INSTANCE = new ReviewingCodeEvaluation();

   /**
    * The name of the {@link Tool} representing no tools.
    */
   public static final String NO_TOOL_NAME = "No Tool";

   /**
    * The name of the {@link Tool} representing 'SED'.
    */
   public static final String SED_TOOL_NAME = "SED";
   
   /**
    * Forbid additional instances.
    */
   private ReviewingCodeEvaluation() {
      super("Reviewing Code", isUIAvailable() ? "data/reviewingCode/instructions/" : null);
   }
   
   @Override
   protected List<Tool> computeTools() {
      URL noToolURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/NoTool.html") : null;
      URL sedURL = isUIAvailable() ? toLocalURL("data/reviewingCode/instructions/SED.html") : null;
      Tool noTool = new Tool(NO_TOOL_NAME, 
                             noToolURL, 
                             noToolURL, 
                             isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_LOGO) : null);
      Tool sed = new Tool(SED_TOOL_NAME, 
                          sedURL, 
                          sedURL, 
                          isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_LOGO) : null);
      return CollectionUtil.toList(noTool, sed);
   }

   @Override
   protected List<AbstractForm> computeForms() {
      FixedForm evaluationForm = new FixedForm("evaluationForm", 
                                               true, 
                                               createStackQuestionPage("middleExample", "Review of IntegerUtil#middle(int, int, int)"));
      return CollectionUtil.toList((AbstractForm)evaluationForm);
   }

   private QuestionPage createStackQuestionPage(String pageName, String title) {
      // New Constructor
      String methodProblemsTitle = "What is wrong?";
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("The created stack is not empty", "StackNotEmpty"), 
                                                             new Choice("Stack can not be filled up to maximal size", "StackSizeWrong"),
                                                             createElseWrongChoice());
      String implementedAsDocumentedTitle = "Does the method implementation operates as specified by its JavaDoc comment?";
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = "Which statement(s) can be executed?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 25: elements = new Object[maximalSize]", "Line 25", true));
      SectionQuestion newConstructor = new SectionQuestion("publicConstructor", 
                                                           "Stack(int)", 
                                                           false, 
                                                           implementedAsDocumented,
                                                           createStackClassInvariantQuestion(true),
                                                           createThrownExceptionsQuestion(),
                                                           executedQuestion,
                                                           createStackLocationQuestion());
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              null,
                              new LabelQuestion("generalDescription", createGeneralDescription("MyInteger#add(MyInteger)")),
                              newConstructor);
   }

   private Choice createElseWrongChoice() {
      return new Choice("Something else is wrong", "SomethingElse", createElseWrongSubQuestion());
   }

   private TextQuestion createElseWrongSubQuestion() {
      String title = "What is wrong?";
      return new TextQuestion("whatsWrong", title, null, new NotUndefinedValueValidator("Question '" + title + "' not answered."), false);
   }
   
   private RadioButtonsQuestion createStackClassInvariantQuestion(boolean constructor) {
      String problemsTitle = "What is wrong?";
      CheckboxQuestion problems = new CheckboxQuestion("classInvariantProblems", 
                                                       problemsTitle, 
                                                       true, 
                                                       null, 
                                                       createNotUndefinedValueValidator(problemsTitle), 
                                                       true,
                                                       new Choice("elements might be null.", "ElementsNull"), 
                                                       new Choice("elements might be non null.", "ElementsNonNull"), 
                                                       new Choice("Element at index < size might be null", "ContainedElementNull"), 
                                                       new Choice("Element at index < size might be non null", "ContainedElementNonNull"), 
                                                       new Choice("Element at index >= size might be null", "NotContainedElementNull"), 
                                                       new Choice("Element at index >= size might be non null", "NotContainedElementNonNull"), 
                                                       new Choice("size might be < 0", "NegativeSize"), 
                                                       new Choice("size might be < elements.length", "SizeLessArrayLength"), 
                                                       new Choice("size might be = elements.length", "SizeEqualArrayLength"), 
                                                       new Choice("size might be > elements.length", "SizeGreaterArrayLength"), 
                                                       createElseWrongChoice());
      String title = constructor ?
                     "Is the class invariant established?" :
                     "Is the class invariant preserved?";
      return new RadioButtonsQuestion("classInvariant", 
                                      title, 
                                      true, 
                                      null, 
                                      createNotUndefinedValueValidator(title), 
                                      true,
                                      new Choice("Yes", "Yes"), 
                                      new Choice("No", "No", problems));
   }

   private CheckboxQuestion createStackLocationQuestion() {
      String title = "Which location(s) of the initial state before method invocation might be changed during execution?";
      return new CheckboxQuestion("changedLocations", 
                                  title, 
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("None", "None"),
                                  new Choice("elements", "elements"),
                                  new Choice("elements[size - 1]", "elements[size - 1]"),
                                  new Choice("elements[size]", "elements[size]"),
                                  new Choice("elements[size + 1]", "elements[size + 1]"),
                                  new Choice("elements[*]", "elements[*]"),
                                  new Choice("elements.length", "elements.length"),
                                  new Choice("size", "size"),
                                  new Choice("something else", "SomethingElse", createElseLocationSubQuestion()));
   }
   
   private TextQuestion createElseLocationSubQuestion() {
      String locationTitle = "Which additional location(s) can be changed?";
      return new TextQuestion("elseLocation", locationTitle, null, new NotUndefinedValueValidator("Question '" + locationTitle + "' not answered."), false);
   }
   
   private RadioButtonsQuestion createThrownExceptionsQuestion() {
      String title = "Is it possible that an exception is thrown?";
      return new RadioButtonsQuestion("exceptionThrown", 
                                      title, 
                                      true, 
                                      null, 
                                      createNotUndefinedValueValidator(title), 
                                      true,
                                      new Choice("Yes", "Yes", createThrownExceptionsSubQuestion()), 
                                      new Choice("No", "No"));
   }
   
   private CheckboxQuestion createThrownExceptionsSubQuestion() {
      String thrownExceptionTitle = "Which exception(s) might be thrown?";
      CheckboxQuestion thrownExceptionQuestion = new CheckboxQuestion("whichExceptionsMightBeThrown", 
                                                                      thrownExceptionTitle, 
                                                                      true,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + thrownExceptionTitle + "' not answered."), 
                                                                      true,
                                                                      new Choice("java.lang.NullPointerException", "java.lang.NullPointerException"),
                                                                      new Choice("java.lang.ArithmeticException", "java.lang.ArithmeticException"),
                                                                      new Choice("java.lang.ArrayIndexOutOfBoundsException", "java.lang.ArrayIndexOutOfBoundsException"),
                                                                      new Choice("java.lang.ArrayStoreException", "java.lang.ArrayStoreException"),
                                                                      new Choice("java.lang.NegativeArraySizeException", "java.lang.NegativeArraySizeException"),
                                                                      new Choice("java.lang.IllegalArgumentException", "java.lang.IllegalArgumentException"),
                                                                      new Choice("java.lang.IllegalStateException", "java.lang.IllegalStateException"),
                                                                      new Choice("something else", "SomethingElse", createElseExceptionSubQuestion()));
      return thrownExceptionQuestion;
   }

   private TextQuestion createElseExceptionSubQuestion() {
      String exceptionTitle = "Which exception is thrown?";
      return new TextQuestion("thrownException", exceptionTitle, null, new NotUndefinedValueValidator("Question '" + exceptionTitle + "' not answered."), false);
   }
   
   private IValueValidator createNotUndefinedValueValidator(String questionTitle) {
      return new NotUndefinedValueValidator("Question '" + questionTitle + "' not answered.");
   }

   private String createGeneralDescription(String method) {
      return "Please inspect the current source code of method '" + method + "' carefully and answer the following questions about it as best as possible.";
   }

   protected String createQuestionPageMessage() {
      return "Please answer the questions to the best of your knowledge.";
   }
}
