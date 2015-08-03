package org.key_project.sed.key.evaluation.model.test.testcase;

import java.util.List;

import org.junit.Test;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.FixedForm;
import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.key.evaluation.model.definition.TestEvaluation;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.input.Trust;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.util.java.CollectionUtil;

/**
 * Tests for {@link EvaluationInputWriter} and {@link EvaluationInputReader}.
 * @author Martin Hentschel
 */
public class FormInputWriterAndReaderTest extends AbstractEvaluationModelTest {
   /**
    * Tests writing and reading of {@link ReviewingCodeEvaluation#INSTANCE}.
    */
   @Test
   public void testReviewingCodeEvaluation() throws Exception {
      AbstractEvaluation evaluation = ReviewingCodeEvaluation.INSTANCE;
      EvaluationInput evaluationInput = new EvaluationInput(evaluation, "keyVersion123", "keyInternalVersionABC");
      for (AbstractFormInput<?> formInput : evaluationInput.getFormInputs()) {
         evaluationInput.setCurrentFormInput(formInput);
         if (formInput.getForm().isCollectTimes()) {
            for (int i = 0; i < formInput.countPageInputs(); i++) {
               AbstractPageInput<?> pageInput = formInput.getPageInput(i);
               if (!pageInput.getPage().isReadonly()) {
                  pageInput.setShownTime(i);
               }
            }
         }
         // Convert to xml
         String xml = EvaluationInputWriter.toFormAnswerXML(formInput);
         // Parse xml
         EvaluationInput parsedInput = EvaluationInputReader.parse(xml);
         AbstractFormInput<?> parsedFormInput = parsedInput.getCurrentFormInput();
         // Compare inputs
         assertNotNull(parsedInput);
         assertNotSame(evaluationInput, parsedInput);
         assertNotNull(parsedFormInput);
         assertNotSame(formInput, parsedFormInput);
         assertFormInput(formInput, parsedFormInput, false);
         // Test complete xml
         doCompleteXmlTest(evaluationInput);
      }
   }
   
   /**
    * Tests writing and reading of {@link UnderstandingProofAttemptsEvaluation#INSTANCE}.
    */
   @Test
   public void testUnderstandingProofAttemptsEvaluation() throws Exception {
      AbstractEvaluation evaluation = UnderstandingProofAttemptsEvaluation.INSTANCE;
      EvaluationInput evaluationInput = new EvaluationInput(evaluation, "keyVersion123", "keyInternalVersionABC");
      for (AbstractFormInput<?> formInput : evaluationInput.getFormInputs()) {
         evaluationInput.setCurrentFormInput(formInput);
         if (formInput.getForm().isCollectTimes()) {
            for (int i = 0; i < formInput.countPageInputs(); i++) {
               AbstractPageInput<?> pageInput = formInput.getPageInput(i);
               if (!pageInput.getPage().isReadonly()) {
                  pageInput.setShownTime(i);
               }
            }
         }
         // Convert to xml
         String xml = EvaluationInputWriter.toFormAnswerXML(formInput);
         // Parse xml
         EvaluationInput parsedInput = EvaluationInputReader.parse(xml);
         AbstractFormInput<?> parsedFormInput = parsedInput.getCurrentFormInput();
         // Compare inputs
         assertNotNull(parsedInput);
         assertNotSame(evaluationInput, parsedInput);
         assertNotNull(parsedFormInput);
         assertNotSame(formInput, parsedFormInput);
         assertFormInput(formInput, parsedFormInput, false);
         // Test complete xml
         doCompleteXmlTest(evaluationInput);
      }
   }
   
   /**
    * Tests the complete storage via {@link EvaluationInputWriter#toXML(EvaluationInput)}.
    * @param evaluationInput The {@link EvaluationInput} to test.
    * @throws Exception Occurred Exception.
    */
   protected void doCompleteXmlTest(EvaluationInput evaluationInput) throws Exception {
      // Covert to complete xml
      String completeXml = EvaluationInputWriter.toXML(evaluationInput);
      // Parse complete xml
      EvaluationInput completeInput = EvaluationInputReader.parse(completeXml);
      // Compare complete inputs
      assertNotSame(evaluationInput, completeInput);
      assertEvaluationInput(evaluationInput, completeInput, false, true, ValueComparison.EQUAL);
   }
   
   /**
    * Test parsings of {@link EvaluationInputWriter#toFormAnswerXML(AbstractFormInput, List)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testAnswersAndRandomOrder() throws Exception {
      doAnswersAndRandomOrder(createFixedInputChanger(100), createFixedOrderComputer());
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
      EvaluationInput evaluationInput = new EvaluationInput(evaluation, "keyVersion123", "keyInternalVersionABC");
      evaluationInput.setUUID("MyUUID");
      evaluationInput.setTimestamp(System.currentTimeMillis());
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
      assertEvaluationInput(evaluationInput, parsedInput, true, false, ValueComparison.EQUAL);
      // Test complete xml
      doCompleteXmlTest(evaluationInput);
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
    * Interface to compute random values.
    * @author Martin Hentschel
    */
   protected static interface IRandomCompletion {
      /**
       * Computes the random values.
       * @param evaluationInput The current {@link EvaluationInput}.
       * @param currentForm The current {@link AbstractFormInput}.
       * @return The computed {@link RandomFormInput}s.
       */
      public List<RandomFormInput> computeRandomValues(EvaluationInput evaluationInput, AbstractFormInput<?> currentForm);
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
      EvaluationInput evaluationInput = new EvaluationInput(evaluation, "keyVersion123", "keyInternalVersionABC");
      evaluationInput.setUUID("MyUUID");
      evaluationInput.setTimestamp(System.currentTimeMillis());
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
      assertEvaluationInput(evaluationInput, parsedInput, true, false, ValueComparison.EQUAL);
   }
   
   /**
    * Test parsing of {@link EvaluationInputWriter#toFormAnswerXML(AbstractFormInput)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testAnswerXmlWithExampleForm_modifiedValues() throws Exception {
      doAnswerTest(createFixedInputChanger(0));
   }
   
   /**
    * Creates an {@link IFormInputChanger} which sets fixed values.
    * @param pageShownTime The shown time to set.
    * @return The created {@link IFormInputChanger}.
    */
   protected IFormInputChanger createFixedInputChanger(final long pageShownTime) {
      return new IFormInputChanger() {
         @Override
         public void changeFormInput(AbstractFormInput<?> formInput) {
            QuestionPageInput pageInput = (QuestionPageInput)formInput.getPageInputs()[0];
            pageInput.setShownTime(pageShownTime);
            assertFalse(pageInput.getQuestionInputs()[0].getQuestion().isEditable()); // Browser
            assertTrue(pageInput.getQuestionInputs()[1].getQuestion().isEditable()); // RadioButtons
            assertTrue(pageInput.getQuestionInputs()[2].getQuestion().isEditable()); // Checkbox
            assertFalse(pageInput.getQuestionInputs()[3].getQuestion().isEditable()); // Label
            assertFalse(pageInput.getQuestionInputs()[4].getQuestion().isEditable()); // Section
            assertTrue(pageInput.getQuestionInputs()[5].getQuestion().isEditable()); // Text
            // Change question 1 (radio)
            QuestionInput radioInput = pageInput.getQuestionInputs()[1];
            radioInput.setValue("This is not a valid radio button value!");
            radioInput.setTrust(Trust.SURE);
            if (pageShownTime > 0) {
               radioInput.setTrustSetAt(111);
               radioInput.setValueSetAt(100);
            }
            // Change yes sub question of radio
            QuestionInput radioChildInput = radioInput.getChoiceInputs(radioInput.getChoices()[0])[0];
            radioChildInput.setValue("two");
            radioChildInput.setTrust(Trust.UNSURE);
            if (pageShownTime > 0) {
               radioInput.setTrustSetAt(4242);
               radioChildInput.setValueSetAt(24);
            }
            // Change question 2 (checkbox)
            QuestionInput checkboxInput = pageInput.getQuestionInputs()[2];
            checkboxInput.setValue("This is not a valid checkbox button value!");
            checkboxInput.setTrust(Trust.EDUCATED_GUESS);
            if (pageShownTime > 0) {
               radioInput.setTrustSetAt(111);
               radioInput.setValueSetAt(100);
            }
            // Change yes sub question of checkbox
            QuestionInput checkboxChildInput = checkboxInput.getChoiceInputs(checkboxInput.getChoices()[0])[0];
            checkboxChildInput.setValue("two");
            checkboxChildInput.setTrust(Trust.UNSURE);
            if (pageShownTime > 0) {
               checkboxInput.setTrustSetAt(4242);
               checkboxChildInput.setValueSetAt(24);
            }
            // Change yes sub question of section
            QuestionInput sectionInput = pageInput.getQuestionInputs()[4];
            QuestionInput sectionChildInput = sectionInput.getChildInputs()[0];
            sectionChildInput.setValue("two");
            sectionChildInput.setTrust(Trust.UNSURE);
            if (pageShownTime > 0) {
               sectionInput.setTrustSetAt(4242);
               sectionChildInput.setValueSetAt(24);
            }
            // Change question 5 (text)
            QuestionInput textInput = pageInput.getQuestionInputs()[5];
            textInput.setValue("This is a valid text value!");
            textInput.setTrust(Trust.SURE);
            if (pageShownTime > 0) {
               textInput.setTrustSetAt(111);
               textInput.setValueSetAt(100);
            }
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
      EvaluationInput evaluationInput = new EvaluationInput(evaluation, "keyVersion123", "keyInternalVersionABC");
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
      assertEvaluationInput(evaluationInput, parsedInput, true, false, ValueComparison.EQUAL);
      // Test complete xml
      doCompleteXmlTest(evaluationInput);
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
}
