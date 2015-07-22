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
                                               createObservableArrayQuestionPage("ObservableArrayExample", "Review of cass ObservableArray"),
                                               createStackQuestionPage("StackExample", "Review of class Stack"));
      return CollectionUtil.toList((AbstractForm)evaluationForm);
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
                              null,
                              new LabelQuestion("generalDescription", createGeneralClassDescription("ObservableArray")),
                              tabbedQuestion);
   }
   
   private TabQuestion createObservableArrayArrayTab() {
      String description = "ObservableArray(Object[]) related question.";
      String methodProblemsTitle = "What is wrong?";
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("Future calls of set(int, Object) will modify the given array", "ArrayModified"), 
                                                             new Choice("Future calls of set(int, Object) will not modify the given array", "ArrayNotModified"), 
                                                             new Choice("ObservableArray is created instead of throwing an exception", "ExceptionMissing"), 
                                                             new Choice("Exception is thrown instead of creating an ObservableArray", "ExceptionThrown"), 
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = "Does the constructor implementation operates as specified by its JavaDoc comment?";
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = "Which statement(s) can be executed?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 30: if (array == null)", "Line 30", true),
                                                               new Choice("Line 31: throw new IllegalArgumentException(\"Array is null.\")", "Line 31", true),
                                                               new Choice("Line 33: this.array = array", "Line 33", true),
                                                               new Choice("Line 34: this.arrayListeners = null", "Line 34", true));
      return new TabQuestion("ObservableArray", 
                             "ObservableArray(Object[])", 
                             false, 
                             implementedAsDocumented,
                             createObservableArrayClassInvariantQuestion(description, true),
                             createThrownExceptionsQuestion(description, false, false, false, true, false, false),
                             executedQuestion,
                             createObservableArrayLocationQuestion(description, true, true, false));
   }
   
   private TabQuestion createSetTab() {
      String description = "set(int, Object) related question.";
      String methodProblemsTitle = "What is wrong?";
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("array[index] is assigned to element", "ArrayUpdated"), 
                                                             new Choice("array[index] is not assigned to element", "ArrayNotUpdated"), 
                                                             new Choice("All ArrayListener of arrayListeners are informed about the change", "ArrayListenerInformed"), 
                                                             new Choice("Not all ArrayListener of arrayListeners are informed about the change", "ArrayListenerNotInformed"), 
                                                             new Choice("An ArrayEvent is created.", "ArrayEventCreated"), 
                                                             new Choice("No ArrayEvent is created.", "ArrayEventNotCreated"), 
                                                             new Choice("The ArrayEvent contains all details about the modification.", "ArrayEventHasDetails"), 
                                                             new Choice("The ArrayEvent does not contains all details about the modification.", "ArrayEventDoesNotHaveDetails"), 
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = "Does the constructor implementation operates as specified by its JavaDoc comment?";
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = "Which statement(s) can be executed?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 49: array[index] = element", "Line 49", true),
                                                               new Choice("Line 50: fireElementChanged(new ArrayEvent(this, index, element))", "Line 50", true),
                                                               new Choice("Line 59: if (arrayListeners != null)", "Line 59", true),
                                                               new Choice("Line 64: int i = 0", "Line 64 initial", true),
                                                               new Choice("Line 64: i < arrayListeners.length", "Line 64 guard", true),
                                                               new Choice("Line 64: i++", "Line 64 increment", true),
                                                               new Choice("Line 65 if (arrayListeners[i] != null)", "Line 65", true),
                                                               new Choice("Line 66 arrayListeners[i].elementChanged(e)", "Line 66", true));
      return new TabQuestion("set", 
                             "set(int, Object)", 
                             false, 
                             implementedAsDocumented,
                             createObservableArrayClassInvariantQuestion(description, false),
                             createThrownExceptionsQuestion(description, true, false, false, false, true, true),
                             executedQuestion,
                             createObservableArrayLocationQuestion(description, false, false, true));
   }
   
   private TabQuestion createSetArrayListenersTab() {
      String description = "setArrayListeners(ArrayListener[]) related question.";
      String methodProblemsTitle = "What is wrong?";
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("ArrayListener are replaced by the new once", "ArrayListenerReplaced"), 
                                                             new Choice("ArrayListener are not replaced by the new once", "ArrayListenerNotReplaced"), 
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = "Does the constructor implementation operates as specified by its JavaDoc comment?";
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = "Which statement(s) can be executed?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 74 this.arrayListeners = arrayListeners", "Line 74", true));
      return new TabQuestion("setArrayListeners", 
                             "setArrayListeners(ArrayListener[])", 
                             false, 
                             implementedAsDocumented,
                             createObservableArrayClassInvariantQuestion(description, false),
                             createThrownExceptionsQuestion(description, false, false, false, false, false, false),
                             executedQuestion,
                             createObservableArrayLocationQuestion(description, false, true, false));
   }
   
   private RadioButtonsQuestion createObservableArrayClassInvariantQuestion(String description, boolean constructor) {
      String problemsTitle = "What is wrong?";
      CheckboxQuestion problems = new CheckboxQuestion("classInvariantProblems", 
                                                       problemsTitle, 
                                                       description,
                                                       true, 
                                                       null, 
                                                       createNotUndefinedValueValidator(problemsTitle), 
                                                       true,
                                                       new Choice("array might be null", "ArrayNull"), 
                                                       new Choice("array might be not null", "ArrayNotNull"), 
                                                       new Choice("array might have length 0", "ArrayLengthZero"), 
                                                       new Choice("array might be empty", "ArrayEmpty"), 
                                                       new Choice("array might be not empty", "ArrayNotEmpty"), 
                                                       new Choice("array might contain null as element", "ArrayContainsNull"), 
                                                       new Choice("array might contain an Object as element", "ArrayContainsObject"), 
                                                       new Choice("arrayListeners might be null", "ArrayListenersNull"), 
                                                       new Choice("arrayListeners might be not null", "ArrayListenersNotNull"), 
                                                       new Choice("arrayListeners might have length 0", "ArrayListenersLengthZero"), 
                                                       new Choice("arrayListeners might be empty", "ArrayListenersEmpty"), 
                                                       new Choice("arrayListeners might be not empty", "ArrayListenersNotEmpty"), 
                                                       new Choice("arrayListeners might contain null as element", "ArrayListenersContainsNull"), 
                                                       new Choice("arrayListeners might contain an Object as element", "ArrayarrayListenersContainsObject"), 
                                                       createElseWrongChoice(description));
      String title = constructor ?
                     "Is the class invariant established?" :
                     "Is the class invariant preserved?";
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

   private CheckboxQuestion createObservableArrayLocationQuestion(String description, boolean expectedArray, boolean expectedArrayListeners, boolean expectedArrayAtIndex) {
      String title = "Which location(s) of the initial state before method invocation might be changed during execution?";
      return new CheckboxQuestion("changedLocations", 
                                  title, 
                                  description,
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
                                  new Choice("None", "None"),
                                  new Choice("array", "array", expectedArray),
                                  new Choice("array[index - 1]", "array[index - 1]"),
                                  new Choice("array[index]", "array[index]", expectedArrayAtIndex),
                                  new Choice("array[index + 1]", "array[index + 1]"),
                                  new Choice("array[*]", "array[*]"),
                                  new Choice("array.length", "array.length"),
                                  new Choice("arrayListeners", "arrayListeners", expectedArrayListeners),
                                  new Choice("arrayListeners[i - 1]", "arrayListeners[i - 1]"),
                                  new Choice("arrayListeners[i]", "arrayListeners[i]"),
                                  new Choice("arrayListeners[i + 1]", "arrayListeners[i + 1]"),
                                  new Choice("arrayListeners[*]", "arrayListeners[*]"),
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
                              null,
                              new LabelQuestion("generalDescription", createGeneralClassDescription("Stack")),
                              tabbedQuestion);
   }
   
   private TabQuestion createStackIntTab() {
      String description = "Stack(int) related question.";
      String methodProblemsTitle = "What is wrong?";
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("The created stack is empty", "StackEmpty"), 
                                                             new Choice("The created stack is not empty", "StackNotEmpty"), 
                                                             new Choice("The created stack can be filled up to maximal size", "StackSizeMaximal"),
                                                             new Choice("The created stack can not be filled up to maximal size", "StackSizeNotMaximal"),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = "Does the constructor implementation operates as specified by its JavaDoc comment?";
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = "Which statement(s) can be executed?";
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
                             "Stack(int)", 
                             false, 
                             implementedAsDocumented,
                             createStackClassInvariantQuestion(description, true, false),
                             createThrownExceptionsQuestion(description, false, true, false, false, false, false),
                             executedQuestion,
                             createStackLocationQuestion(description, true, true, false));
   }
   
   private TabQuestion createStackStackTab() {
      String description = "Stack(Stack) related question.";
      String methodProblemsTitle = "What is wrong?";
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("The created stack is empty", "StackEmpty"), 
                                                             new Choice("The created stack is not empty", "StackNotEmpty"), 
                                                             new Choice("The created stack provides same content as the existing once", "SameContent"),
                                                             new Choice("The created stack provides different content as the existing once", "DifferentContent"),
                                                             new Choice("The created stack has same size as the existing once", "SameSize"),
                                                             new Choice("The created stack has different size as the existing once", "DifferentSize"),
                                                             new Choice("The created stack has same elements array as the existing once", "SameElements", true),
                                                             new Choice("The created stack has different elements array as the existing once", "DifferentElements"),
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = "Does the constructor implementation operates as specified by its JavaDoc comment?";
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes"), 
                                                                              new Choice("No", "No", true, methodProblems));
      String executedTitle = "Which statement(s) can be executed?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 43: this.elements = existingStack.elements", "Line 43", true),
                                                               new Choice("Line 44: this.size = existingStack.size", "Line 44", true));
      return new TabQuestion("Stack_Stack", 
                             "Stack(Stack)", 
                             false, 
                             implementedAsDocumented,
                             createStackClassInvariantQuestion(description, true, false),
                             createThrownExceptionsQuestion(description, true, false, false, false, false, false),
                             executedQuestion,
                             createStackLocationQuestion(description, true, true, false));
   }
   
   private TabQuestion createPushTab() {
      String description = "push(Object) related question.";
      String methodProblemsTitle = "What is wrong?";
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("size is increased by 1", "SizeIncreased"), 
                                                             new Choice("size is not updated", "SizeNotUpdated"), 
                                                             new Choice("elements is replaced by a different array", "ElementsChanged"), 
                                                             new Choice("elements is not updated", "ElementsNotUpdated"), 
                                                             new Choice("Element at index size is replaced", "ElementAtSizeReplaced"), 
                                                             new Choice("Element at index size + 1 is replaced", "ElementAtSizePlusOneReplaced"), 
                                                             new Choice("Exception is thrown instead of updating the stack", "ExceptionThrown"), 
                                                             new Choice("Stack is updated instead of throwing an exception", "ExceptionNOtThrown"), 
                                                             new Choice("Executing pop after push would not return the added element.", "PushPopBroken"), 
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = "Does the method implementation operates as specified by its JavaDoc comment?";
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String executedTitle = "Which statement(s) can be executed?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 55: if (size < elements.length)", "Line 55", true),
                                                               new Choice("Line 56: elements[size++] = e", "Line 56", true),
                                                               new Choice("Line 59: throw new IllegalStateException(\"Stack is full.\")", "Line 59", true));
      return new TabQuestion("push(Object)", 
                             "push(Object)", 
                             false, 
                             implementedAsDocumented,
                             createStackClassInvariantQuestion(description, false, false),
                             createThrownExceptionsQuestion(description, false, false, true, false, false, false),
                             executedQuestion,
                             createStackLocationQuestion(description, false, true, true));
   }
   
   private TabQuestion createPopTab() {
      String description = "pop() related question.";
      String methodProblemsTitle = "What is wrong?";
      CheckboxQuestion methodProblems = new CheckboxQuestion("methodProblems", 
                                                             methodProblemsTitle, 
                                                             description,
                                                             true, 
                                                             null, 
                                                             createNotUndefinedValueValidator(methodProblemsTitle), 
                                                             true,
                                                             new Choice("size is decreased by 1", "SizeDecrease"), 
                                                             new Choice("size is not updated", "SizeNotUpdated"), 
                                                             new Choice("elements is replaced by a different array", "ElementsChanged"), 
                                                             new Choice("elements is not updated", "ElementsNotUpdated"), 
                                                             new Choice("Element at index size is returned", "ElementAtSizeReturned"), 
                                                             new Choice("Element at index size - 1 is returned", "ElementAtSizePlusOneReturned"), 
                                                             new Choice("Exception is thrown instead of returning the top element", "ExceptionThrown"), 
                                                             new Choice("Top element is returned instead of throwing an exception", "ExceptionNOtThrown"), 
                                                             new Choice("Executing pop twice would return the same element twice.", "PopPopBroken"), 
                                                             createElseWrongChoice(description));
      String implementedAsDocumentedTitle = "Does the method implementation operates as specified by its JavaDoc comment?";
      RadioButtonsQuestion implementedAsDocumented = new RadioButtonsQuestion("implementedAsDocumented", 
                                                                              implementedAsDocumentedTitle, 
                                                                              description,
                                                                              true, 
                                                                              null, 
                                                                              createNotUndefinedValueValidator(implementedAsDocumentedTitle), 
                                                                              true,
                                                                              new Choice("Yes", "Yes", true), 
                                                                              new Choice("No", "No", methodProblems));
      String returnValueTitle = "Which claims about the returned value are true?";
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
      String executedTitle = "Which statement(s) can be executed?";
      CheckboxQuestion executedQuestion = new CheckboxQuestion("executedStatements", 
                                                               executedTitle, 
                                                               description,
                                                               true,
                                                               null, 
                                                               new NotUndefinedValueValidator("Question '" + executedTitle + "' not answered."), 
                                                               true,
                                                               new Choice("None of the statements can be executed", "None"),
                                                               new Choice("Line 71: if (size >= 1)", "Line 71", true),
                                                               new Choice("Line 72: return elements[--size]", "Line 72", true),
                                                               new Choice("Line 75: throw new IllegalStateException(\"Stack is empty.\")", "Line 75", true));
      return new TabQuestion("pop()", 
                             "pop()", 
                             false, 
                             implementedAsDocumented,
                             createStackClassInvariantQuestion(description, false, true),
                             createThrownExceptionsQuestion(description, false, false, true, false, false, false),
                             executedQuestion,
                             createStackLocationQuestion(description, false, true, false),
                             returnValue);
   }

   private Choice createElseWrongChoice(String description) {
      return new Choice("Something else is wrong", "SomethingElse", createElseWrongSubQuestion(description));
   }

   private TextQuestion createElseWrongSubQuestion(String description) {
      String title = "What is wrong?";
      return new TextQuestion("whatsWrong", title, description, null, new NotUndefinedValueValidator("Question '" + title + "' not answered."), false);
   }
   
   private RadioButtonsQuestion createStackClassInvariantQuestion(String description, boolean constructor, boolean expectedMemoryLeak) {
      String problemsTitle = "What is wrong?";
      CheckboxQuestion problems = new CheckboxQuestion("classInvariantProblems", 
                                                       problemsTitle, 
                                                       description,
                                                       true, 
                                                       null, 
                                                       createNotUndefinedValueValidator(problemsTitle), 
                                                       true,
                                                       new Choice("elements might be null.", "ElementsNull"), 
                                                       new Choice("elements might be non null.", "ElementsNonNull"), 
                                                       new Choice("elements might be of type Object[].", "ElementsTypeObjectArray"), 
                                                       new Choice("elements might be not of type Object[].", "ElementsTypeNotObjectArray"), 
                                                       new Choice("Element at index < size might be null", "ContainedElementNull"), 
                                                       new Choice("Element at index < size might be non null", "ContainedElementNonNull"), 
                                                       new Choice("Element at index >= size might be null", "NotContainedElementNull"), 
                                                       new Choice("Element at index >= size might be non null", "NotContainedElementNonNull", expectedMemoryLeak), 
                                                       new Choice("size might be < 0", "NegativeSize"), 
                                                       new Choice("size might be < elements.length", "SizeLessArrayLength"), 
                                                       new Choice("size might be = elements.length", "SizeEqualArrayLength"), 
                                                       new Choice("size might be > elements.length", "SizeGreaterArrayLength"), 
                                                       createElseWrongChoice(description));
      String title = constructor ?
                     "Is the class invariant established?" :
                     "Is the class invariant preserved?";
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

   private CheckboxQuestion createStackLocationQuestion(String description, boolean expectedElements, boolean expectedSize, boolean expectedElementAtPlus1) {
      String title = "Which location(s) of the initial state before method invocation might be changed during execution?";
      return new CheckboxQuestion("changedLocations", 
                                  title, 
                                  description,
                                  true,
                                  null, 
                                  new NotUndefinedValueValidator("Question '" + title + "' not answered."), 
                                  true,
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
      return new TextQuestion("elseLocation", locationTitle, description, null, new NotUndefinedValueValidator("Question '" + locationTitle + "' not answered."), false);
   }
   
   private RadioButtonsQuestion createThrownExceptionsQuestion(String description, boolean expectedNPE, boolean expectedNASE, boolean expectedISE, boolean expectedIAE, boolean expectedAIOOBE, boolean expectedASE) {
      String title = "Is it possible that an exception is thrown?";
      return new RadioButtonsQuestion("exceptionThrown", 
                                      title, 
                                      description,
                                      true, 
                                      null, 
                                      createNotUndefinedValueValidator(title), 
                                      true,
                                      new Choice("Yes", "Yes", !expectedNPE && !expectedNASE && !expectedISE, createThrownExceptionsSubQuestion(description, expectedNPE, expectedNASE, expectedISE, expectedIAE, expectedAIOOBE, expectedASE)), 
                                      new Choice("No", "No"));
   }
   
   private CheckboxQuestion createThrownExceptionsSubQuestion(String description, boolean expectedNPE, boolean expectedNASE, boolean expectedISE, boolean expectedIAE, boolean expectedAIOOBE, boolean expectedASE) {
      String thrownExceptionTitle = "Which exception(s) might be thrown?";
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
      return new TextQuestion("thrownException", exceptionTitle, description, null, new NotUndefinedValueValidator("Question '" + exceptionTitle + "' not answered."), false);
   }
   
   private IValueValidator createNotUndefinedValueValidator(String questionTitle) {
      return new NotUndefinedValueValidator("Question '" + questionTitle + "' not answered.");
   }

   private String createGeneralClassDescription(String className) {
      return "Please inspect the current source code of class '" + className + "' carefully and answer the following questions about it as best as possible.";
   }

   protected String createQuestionPageMessage() {
      return "Please answer the questions to the best of your knowledge.";
   }
}
