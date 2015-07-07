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
      Tool noTool = new Tool(NO_TOOL_NAME, noToolURL, isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.KEY_LOGO) : null);
      Tool sed = new Tool(SED_TOOL_NAME, sedURL, isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.SED_LOGO) : null);
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
      String emptyStackTitle = "Is the created stack empty?";
      RadioButtonsQuestion emptyStack = new RadioButtonsQuestion("emptyStack", 
                                                                 emptyStackTitle, 
                                                                 true, 
                                                                 null, 
                                                                 createNotUndefinedValueValidator(emptyStackTitle), 
                                                                 true,
                                                                 new Choice("Yes", "Yes"), 
                                                                 new Choice("No", "No"));
      String maxSizeTitle = "Can the created stack be filled up to the specified maximal stack size?";
      RadioButtonsQuestion maxSize = new RadioButtonsQuestion("maxSize", 
                                                              maxSizeTitle, 
                                                              true, 
                                                              null, 
                                                              createNotUndefinedValueValidator(maxSizeTitle), 
                                                              true,
                                                              new Choice("Yes", "Yes"), 
                                                              new Choice("No", "No"));
      String line25Title = "Is it possible to execute line 25 (elements = new Object[maximalSize])?";
      RadioButtonsQuestion line25 = new RadioButtonsQuestion("line25Executable", 
                                                             line25Title, 
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(line25Title), 
                                                             true,
                                                             new Choice("Yes", "Yes"), 
                                                             new Choice("No", "No"));
      SectionQuestion newConstructor = new SectionQuestion("publicConstructor", 
                                                           "Stack(int)", 
                                                           false, 
                                                           emptyStack, 
                                                           maxSize, 
                                                           line25,
                                                           createThrownExceptionsQuestion());
      return new QuestionPage(pageName, 
                              title, 
                              createQuestionPageMessage(), 
                              true,
                              true,
                              null,
                              new LabelQuestion("generalDescription", createGeneralDescription("MyInteger#add(MyInteger)")),
                              newConstructor);
   }
   
   private CheckboxQuestion createThrownExceptionsQuestion() {
      String thrownExceptionTitle = "Which exception(s) might be thrown?";
      CheckboxQuestion thrownExceptionQuestion = new CheckboxQuestion("whichExceptionsMightBeThrown", 
                                                                      thrownExceptionTitle, 
                                                                      true,
                                                                      null, 
                                                                      new NotUndefinedValueValidator("Question '" + thrownExceptionTitle + "' not answered."), 
                                                                      true,
                                                                      new Choice("No Exceptions possible", "No Exceptions possible"),
                                                                      new Choice("java.lang.NullPointerException", "java.lang.NullPointerException"),
                                                                      new Choice("java.lang.ArithmeticException", "java.lang.ArithmeticException"),
                                                                      new Choice("java.lang.ArrayIndexOutOfBoundsException", "java.lang.ArrayIndexOutOfBoundsException"),
                                                                      new Choice("java.lang.ArrayStoreException", "java.lang.ArrayStoreException"),
                                                                      new Choice("java.lang.IllegalArgumentException", "java.lang.IllegalArgumentException"),
                                                                      new Choice("java.lang.IllegalStateException", "java.lang.IllegalStateException"));
      return thrownExceptionQuestion;
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
