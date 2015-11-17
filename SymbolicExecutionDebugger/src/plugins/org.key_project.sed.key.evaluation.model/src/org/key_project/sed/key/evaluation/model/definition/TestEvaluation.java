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
   public static final TestEvaluation INSTANCE = new TestEvaluation();

   /**
    * The name of the first tool.
    */
   public static final String TOOL_1_NAME = "tool1";

   /**
    * The name of the second tool.
    */
   public static final String TOOL_2_NAME = "tool2";
   
   private TestEvaluation() {
      super("Test Evaluation", null);
   }

   @Override
   protected List<AbstractForm> computeForms() {
      try {
         RadioButtonsQuestion yesSubQuestion = new RadioButtonsQuestion("yesSubQuestions", "yesSubQuestionsLabel", true, "one", new FixedValueValidator("one", "errorMessage"), false, new Choice("one", "one"), new Choice("two", "two"), new Choice("three", "three"));
         QuestionPage questionPage = new QuestionPage("questionPage", 
                                                      "questionPageTitle", 
                                                      "questionPageMessage",
                                                      false,
                                                      false,
                                                      null,
                                                      new BrowserQuestion("browserQuestion", new URL("http://key-project.org/")),
                                                      new RadioButtonsQuestion("radioQuestions", "radioQuestionsLabel", false, "no", new FixedValueValidator("yes", "errorMessage"), true, new Choice("Yes", "yes", yesSubQuestion), new Choice("No", "no")),
                                                      new CheckboxQuestion("checkboxQuestion", "checkboxQuestionLabel", false, "option1", new FixedValueValidator("option2", "errorMessage"), true, new Choice("option2", "option2", yesSubQuestion), new Choice("option1", "option1")),
                                                      new LabelQuestion("labelQuestion", "labelQuestionLabel"),
                                                      new SectionQuestion("sectionQuestion", "sectionQuestionLabel", false, yesSubQuestion),
                                                      new TextQuestion("textQuestion", "textQuestionLabel", null, null, false, -1, -1));
         SendFormPage sendFixedPage = new SendFormPage("sendFixedPage", "sendFixedPageTitle", "sendFixedPageMessage", "additionalDataCollectedByServer");
         FixedForm fixedForm = new FixedForm("fixedForm", false, questionPage, sendFixedPage);
         InstructionPage instructionPage = new InstructionPage("instructionPage", "instructionPageTitle", "instructionPageMessage", new URL("http://key-project.org/"), null);
         ToolPage tool1Page = new ToolPage(getTool(TOOL_1_NAME), null, false);
         QuestionPage random1Page = new QuestionPage("random1Page", "random1PageTitle", "random1PageMessage", false, false, null);
         QuestionPage random2Page = new QuestionPage("random2Page", "random2PageTitle", "random2PageMessage", false, false, null);
         QuestionPage random3Page = new QuestionPage("random3Page", "random3PageTitle", "random3PageMessage", false, false, null);
         SendFormPage sendRandomPage = new SendFormPage("sendRandomPage", "sendRandomPageTitle", "sendRandomPageMessage", "additionalDataCollectedByServer");
         RandomForm randomForm = new RandomForm("randomForm", true, instructionPage, tool1Page, random1Page, random2Page, random3Page, sendRandomPage);
         return CollectionUtil.toList(fixedForm, randomForm);
      }
      catch (MalformedURLException e) {
         throw new IllegalArgumentException(e);
      }
   }

   @Override
   protected List<Tool> computeTools() {
      Tool t1 = new Tool(TOOL_1_NAME, null, null, null);
      Tool t2 = new Tool(TOOL_2_NAME, null, null, null);
      return CollectionUtil.toList(t1, t2);
   }
}
