package org.key_project.sed.key.evaluation.model.test.testcase;

import java.util.Iterator;
import java.util.List;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.FixedForm;
import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.TestEvaluation;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.FixedFormInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.input.SendFormPageInput;
import org.key_project.sed.key.evaluation.model.input.ToolPageInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.sed.key.evaluation.model.random.IRandomCompletion;
import org.key_project.util.java.CollectionUtil;

/**
 * Tests for {@link EvaluationInputWriter} and {@link EvaluationInputReader}.
 * @author Martin Hentschel
 */
public class FormInputWriterAndReaderTest extends TestCase {
   /**
    * Tests writing and reading of {@link UnderstandingProofAttemptsEvaluation#INSTANCE}.
    */
   @Test
   public void testUnderstandingProofAttemptsEvaluation() throws Exception {
      AbstractEvaluation evaluation = UnderstandingProofAttemptsEvaluation.INSTANCE;
      EvaluationInput evaluationInput = new EvaluationInput(evaluation);
      for (AbstractFormInput<?> formInput : evaluationInput.getFormInputs()) {
         evaluationInput.setCurrentFormInput(formInput);
         // Convert to xml
         String xml = EvaluationInputWriter.toFormAnswerXML(formInput);
         // Parse xml
         EvaluationInput parsedInput = EvaluationInputReader.parse(xml);
         // Compare inputs
         assertNotNull(parsedInput);
         assertNotSame(evaluationInput, parsedInput);
         assertEvaluationInput(evaluationInput, parsedInput);
      }
   }
   
   /**
    * Test parsings of {@link EvaluationInputWriter#toFormAnswerXML(AbstractFormInput, List)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testAnswersAndRandomOrder() throws Exception {
      doAnswersAndRandomOrder(createFixedInputChanger(), createFixedOrderComputer());
   }
   
   /**
    * Performs the test steps to test parsing of {@link EvaluationInputWriter#toFormAnswerXML(AbstractFormInput, List)}.
    * @param changer The {@link IFormInputChanger} to use.
    * @param computer The {@link IRandomCompletion} to use.
    * @throws Exception Occurred Exception.
    */
   protected void doAnswersAndRandomOrder(IFormInputChanger changer,
                                          IRandomCompletion computer) throws Exception {
      // Create example form
      AbstractEvaluation evaluation = TestEvaluation.INSTANCE;
      FixedForm fixedForm = (FixedForm) evaluation.getForms()[0];
      RandomForm randomForm = (RandomForm) evaluation.getForms()[1];
      // Create inputs
      EvaluationInput evaluationInput = new EvaluationInput(evaluation);
      evaluationInput.setUUID("MyUUID");
      AbstractFormInput<?> fixedFormInput = evaluationInput.getFormInput(fixedForm);
      evaluationInput.setCurrentFormInput(fixedFormInput);
      if (changer != null) {
         changer.changeFormInput(fixedFormInput);
      }
      AbstractFormInput<?> randomFormInput = evaluationInput.getFormInput(randomForm);
      // Convert to xml
      List<RandomFormInput> updatedOrders = computer != null ? 
                                            computer.computeRandomValues(evaluationInput, randomFormInput) : 
                                            null;
      String xml = EvaluationInputWriter.toFormAnswerXML(fixedFormInput, updatedOrders);
      // Parse xml
      EvaluationInput parsedInput = EvaluationInputReader.parse(xml);
      // Compare inputs
      assertNotNull(parsedInput);
      assertNotSame(evaluationInput, parsedInput);
      assertEvaluationInput(evaluationInput, parsedInput);
   }
   
   /**
    * Test parsing of {@link EvaluationInputWriter#toRandomOrderXML(EvaluationInput, List)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testRandomOrder_UUID_and_SpecifiedOrder() throws Exception {
      doRandomOrderTest(createFixedOrderComputer());
   }
   
   /**
    * Creates a {@link IRandomCompletion} which returns a fixed order.
    * @return The created {@link IRandomCompletion}.
    */
   protected IRandomCompletion createFixedOrderComputer() {
      return new IRandomCompletion() {
         @SuppressWarnings("unchecked")
         @Override
         public List<RandomFormInput> computeRandomValues(EvaluationInput evaluationInput, AbstractFormInput<?> currentForm) {
            RandomFormInput formInput = (RandomFormInput)evaluationInput.getFormInputs()[1];
            AbstractPageInput<?> page1 = formInput.getPageInputs()[0];
            AbstractPageInput<?> page2 = formInput.getPageInputs()[1];
            AbstractPageInput<?> page3 = formInput.getPageInputs()[2];
            formInput.setPageOrder(CollectionUtil.toList(page3, page1, page2));
            formInput.setTool(page1, currentForm.getEvaluationInput().getEvaluation().getTools()[0]);
            formInput.setTool(page2, currentForm.getEvaluationInput().getEvaluation().getTools()[1]);
            return CollectionUtil.toList(formInput);
         }
      };
   }
   
   /**
    * Test parsing of {@link EvaluationInputWriter#toRandomOrderXML(EvaluationInput, List)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testRandomOrder_onlyUUID() throws Exception {
      doRandomOrderTest(null);
   }
   
   /**
    * Performs the test steps to test parsing of {@link EvaluationInputWriter#toRandomOrderXML(EvaluationInput, List)}.
    * @param computer The {@link IRandomCompletion} to use.
    * @throws Exception Occurred Exception.
    */
   protected void doRandomOrderTest(IRandomCompletion computer) throws Exception {
      // Create example form
      AbstractEvaluation evaluation = TestEvaluation.INSTANCE;
      RandomForm randomForm = (RandomForm) evaluation.getForms()[1];
      // Create inputs
      EvaluationInput evaluationInput = new EvaluationInput(evaluation);
      evaluationInput.setUUID("MyUUID");
      AbstractFormInput<?> randomFormInput = evaluationInput.getFormInput(randomForm);
      // Convert to xml
      List<RandomFormInput> updatedOrders = computer != null ? 
                                            computer.computeRandomValues(evaluationInput, randomFormInput) : 
                                            null;
      String xml = EvaluationInputWriter.toRandomOrderXML(evaluationInput, updatedOrders);
      // Parse xml
      EvaluationInput parsedInput = EvaluationInputReader.parse(xml);
      // Compare inputs
      assertNotNull(parsedInput);
      assertNotSame(evaluationInput, parsedInput);
      assertEvaluationInput(evaluationInput, parsedInput);
   }
   
   /**
    * Test parsing of {@link EvaluationInputWriter#toFormAnswerXML(AbstractFormInput)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testAnswerXmlWithExampleForm_modifiedValues() throws Exception {
      doAnswerTest(createFixedInputChanger());
   }
   
   /**
    * Creates an {@link IFormInputChanger} which sets fixed values.
    * @return The created {@link IFormInputChanger}.
    */
   protected IFormInputChanger createFixedInputChanger() {
      return new IFormInputChanger() {
         @Override
         public void changeFormInput(AbstractFormInput<?> formInput) {
            QuestionPageInput pageInput = (QuestionPageInput)formInput.getPageInputs()[0];
            assertFalse(pageInput.getQuestionInputs()[0].getQuestion().isEditable()); // Browser
            assertTrue(pageInput.getQuestionInputs()[1].getQuestion().isEditable()); // RadioButtons
            // Change question 1
            QuestionInput radioInput = pageInput.getQuestionInputs()[1];
            radioInput.setValue("This is not a valid radio button value!");
            radioInput.setTrust(Boolean.TRUE);
            // Change yes sub question
            QuestionInput childInput = radioInput.getChoiceInputs(radioInput.getChoices()[0])[0];
            childInput.setValue("two");
            childInput.setTrust(Boolean.FALSE);
         }         
      };
   }
   
   /**
    * Test parsing of {@link EvaluationInputWriter#toFormAnswerXML(AbstractFormInput)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testAnswerXmlWithExampleForm_defaultValues() throws Exception {
      doAnswerTest(null);
   }
   
   /**
    * Performs the test steps to test parsing of {@link EvaluationInputWriter#toFormAnswerXML(AbstractFormInput)}.
    * @param changer The {@link IFormInputChanger} to use.
    * @throws Exception Occurred Exception.
    */
   protected void doAnswerTest(IFormInputChanger changer) throws Exception {
      // Create example form
      AbstractEvaluation evaluation = TestEvaluation.INSTANCE;
      FixedForm fixedForm = (FixedForm) evaluation.getForms()[0];
      // Create inputs
      EvaluationInput evaluationInput = new EvaluationInput(evaluation);
      AbstractFormInput<?> fixedFormInput = evaluationInput.getFormInput(fixedForm);
      evaluationInput.setCurrentFormInput(fixedFormInput);
      if (changer != null) {
         changer.changeFormInput(fixedFormInput);
      }
      // Convert to xml
      String xml = EvaluationInputWriter.toFormAnswerXML(fixedFormInput);
      // Parse xml
      EvaluationInput parsedInput = EvaluationInputReader.parse(xml);
      // Compare inputs
      assertNotNull(parsedInput);
      assertNotSame(evaluationInput, parsedInput);
      assertEvaluationInput(evaluationInput, parsedInput);
   }
   
   /**
    * Allows to modify a given {@link AbstractFormInput}.
    * @author Martin Hentschel
    */
   protected static interface IFormInputChanger {
      /**
       * Modifies the given {@link AbstractFormInput}.
       * @param formInput The {@link AbstractFormInput} to modify.
       */
      public void changeFormInput(AbstractFormInput<?> formInput);
   }

   /**
    * Ensures that the given {@link EvaluationInput}s are equal.
    * @param expected The expected {@link EvaluationInput}.
    * @param actual The actual {@link EvaluationInput}.
    */
   protected void assertEvaluationInput(EvaluationInput expected, EvaluationInput actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertNotSame(expected, actual);
         assertEquals(expected.getEvaluation().getName(), actual.getEvaluation().getName());
         assertEquals(expected.getUUID(), actual.getUUID());
         assertFormInput(expected.getCurrentFormInput(), actual.getCurrentFormInput());
         assertFormInputs(expected.getFormInputs(), actual.getFormInputs());
      }
      else {
         assertNull(actual);
      }
   }

   /**
    * Ensures that the given {@link AbstractFormInput}s are equal.
    * @param expected The expected {@link AbstractFormInput}s.
    * @param actual The actual {@link AbstractFormInput}s.
    */
   protected void assertFormInputs(AbstractFormInput<?>[] expected, AbstractFormInput<?>[] actual) {
      assertNotNull(expected);
      assertNotNull(actual);
      assertEquals(expected.length, actual.length);
      for (int i = 0; i < expected.length; i++) {
         assertFormInput(expected[i], actual[i]);
      }
   }

   /**
    * Ensures that the given {@link AbstractFormInput}s are equal.
    * @param expected The expected {@link AbstractFormInput}.
    * @param actual The actual {@link AbstractFormInput}.
    */
   protected void assertFormInput(AbstractFormInput<?> expected, AbstractFormInput<?> actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertNotSame(expected, actual);
         assertEquals(expected.getForm(), actual.getForm());
         assertPageInputs(expected.getPageInputs(), actual.getPageInputs());
         if (expected instanceof RandomFormInput) {
            assertTrue(actual instanceof RandomFormInput);
            assertPageInputs(((RandomFormInput) expected).getPageOrder(), ((RandomFormInput) actual).getPageOrder());
            assertTools((RandomFormInput) expected, (RandomFormInput) actual);
         }
         else if (expected instanceof FixedFormInput) {
            assertTrue(actual instanceof FixedFormInput);
         }
         else {
            fail("Unsupported form input: " + expected);
         }
      }
      else {
         assertNull(actual);
      }
   }

   /**
    * Ensures that the given {@link Tool}s are equal.
    * @param expected The expected {@link Tool}s.
    * @param actual The actual {@link Tool}s.
    */
   protected void assertTools(RandomFormInput expected, RandomFormInput actual) {
      assertNotNull(expected);
      assertNotNull(actual);
      for (AbstractPageInput<?> expectedPageInput : expected.getPageInputs()) {
         AbstractPageInput<?> actualPageInput = actual.getPageInput(expectedPageInput.getPage());
         assertTool(expected.getTool(expectedPageInput), actual.getTool(actualPageInput));
      }
      for (AbstractPageInput<?> actualPageInput : actual.getPageInputs()) {
         AbstractPageInput<?> expectedPageInput = expected.getPageInput(actualPageInput.getPage());
         assertTool(expected.getTool(expectedPageInput), actual.getTool(actualPageInput));
      }
   }

   /**
    * Ensures that the given {@link Tool}s are equal.
    * @param expected The expected {@link Tool}s.
    * @param actual The actual {@link Tool}s.
    */
   private void assertTool(Tool expected, Tool actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertEquals(expected.getName(), actual.getName());
      }
      else {
         assertNull(actual);
      }
   }

   /**
    * Ensures that the given {@link AbstractPageInput}s are equal.
    * @param expected The expected {@link AbstractPageInput}s.
    * @param actual The actual {@link AbstractPageInput}s.
    */
   protected void assertPageInputs(List<AbstractPageInput<?>> expected, List<AbstractPageInput<?>> actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertEquals(expected.size(), actual.size());
         Iterator<AbstractPageInput<?>> expectedIter = expected.iterator();
         Iterator<AbstractPageInput<?>> actualIter = actual.iterator();
         while (expectedIter.hasNext() && actualIter.hasNext()) {
            assertPageInput(expectedIter.next(), actualIter.next());
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(actualIter.hasNext());
      }
      else {
         assertNull(actual);
      }
   }

   /**
    * Ensures that the given {@link AbstractPageInput}s are equal.
    * @param expected The expected {@link AbstractPageInput}s.
    * @param actual The actual {@link AbstractPageInput}s.
    */
   protected void assertPageInputs(AbstractPageInput<?>[] expected, AbstractPageInput<?>[] actual) {
      assertNotNull(expected);
      assertNotNull(actual);
      assertEquals(expected.length, actual.length);
      for (int i = 0; i < expected.length; i++) {
         assertPageInput(expected[i], actual[i]);
      }
   }

   /**
    * Ensures that the given {@link AbstractPageInput}s are equal.
    * @param expected The expected {@link AbstractPageInput}.
    * @param actual The actual {@link AbstractPageInput}.
    */
   protected void assertPageInput(AbstractPageInput<?> expected, AbstractPageInput<?> actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertNotSame(expected, actual);
         assertEquals(expected.getPage(), actual.getPage());
         if (expected instanceof QuestionPageInput) {
            assertTrue(actual instanceof QuestionPageInput);
            assertQuestionInputs(((QuestionPageInput) expected).getQuestionInputs(), ((QuestionPageInput) actual).getQuestionInputs());
         }
         else if (expected instanceof SendFormPageInput) {
            assertTrue(actual instanceof SendFormPageInput);
            // Nothing else to do as accept state is not stored
         }
         else if (expected instanceof ToolPageInput) {
            assertTrue(actual instanceof ToolPageInput);
            // Nothing else to do as nothing is stored
         }
         else {
            fail("Unsupported page input '" + expected.getClass() + "'.");
         }
      }
      else {
         assertNull(actual);
      }
   }

   /**
    * Ensures that the given {@link QuestionInput}s are equal.
    * @param expected The expected {@link QuestionInput}s.
    * @param actual The actual {@link QuestionInput}s.
    */
   protected void assertQuestionInputs(QuestionInput[] expected, QuestionInput[] actual) {
      assertNotNull(expected);
      assertNotNull(actual);
      assertEquals(expected.length, actual.length);
      for (int i = 0; i < expected.length; i++) {
         assertQuestionInput(expected[i], actual[i]);
      }
   }

   /**
    * Ensures that the given {@link QuestionInput}s are equal.
    * @param expected The expected {@link QuestionInput}.
    * @param actual The actual {@link QuestionInput}.
    */
   protected void assertQuestionInput(QuestionInput expected, QuestionInput actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertNotSame(expected, actual);
         assertEquals(expected.getQuestion(), actual.getQuestion());
         assertEquals(expected.getValue(), actual.getValue());
         assertEquals(expected.getTrust(), actual.getTrust());
         assertEquals(expected.hasChoiceInputs(), actual.hasChoiceInputs());
         if (expected.hasChoiceInputs()) {
            for (Choice choice : expected.getChoices()) {
               assertQuestionInputs(expected.getChoiceInputs(choice), actual.getChoiceInputs(choice));
            }
         }
      }
      else {
         assertNull(actual);
      }
   }
}
