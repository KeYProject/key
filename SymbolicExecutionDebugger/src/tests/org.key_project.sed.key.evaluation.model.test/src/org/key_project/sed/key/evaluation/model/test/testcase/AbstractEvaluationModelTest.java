package org.key_project.sed.key.evaluation.model.test.testcase;

import java.util.Iterator;
import java.util.List;

import junit.framework.TestCase;

import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.FixedFormInput;
import org.key_project.sed.key.evaluation.model.input.InstructionPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.input.SendFormPageInput;
import org.key_project.sed.key.evaluation.model.input.ToolPageInput;
import org.key_project.sed.key.evaluation.model.input.Trust;
import org.key_project.util.java.CollectionUtil;

/**
 * Provides basic functionality to test an evaluation model.
 * @author Martin Hentschel
 */
public class AbstractEvaluationModelTest extends TestCase {
   /**
    * Possible options to compare values.
    * @author Martin Hentschel
    */
   public static enum ValueComparison {
      /**
       * Values should be equal.
       */
      EQUAL,
      
      /**
       * Value should not be set.
       */
      NOT_SET,
      
      /**
       * Value should be set.
       */
      SET,
      
      /**
       * Do not compare values.
       */
      IGNORE
   }
   
   /**
    * Ensures that the given {@link EvaluationInput}s are equal.
    * @param expected The expected {@link EvaluationInput}.
    * @param actual The actual {@link EvaluationInput}.
    * @param assertKeYVersions Check KeY versions?
    * @param assertCurrentPage Check current page?
    */
   public void assertEvaluationInput(EvaluationInput expected, EvaluationInput actual, boolean assertKeYVersions, boolean assertCurrentPage, ValueComparison timestampComparison) {
      if (expected != null) {
         assertNotNull(actual);
         assertNotSame(expected, actual);
         assertEquals(expected.getEvaluation().getName(), actual.getEvaluation().getName());
         assertEquals(expected.getUUID(), actual.getUUID());
         if (ValueComparison.EQUAL.equals(timestampComparison)) {
            assertEquals(expected.getTimestamp(), actual.getTimestamp());
         }
         else if (ValueComparison.NOT_SET.equals(timestampComparison)) {
            assertSame(0, expected.getTimestamp());
            assertSame(0, actual.getTimestamp());
         }
         else if (ValueComparison.SET.equals(timestampComparison)) {
            assertNotSame(0, expected.getTimestamp());
            assertNotSame(0, actual.getTimestamp());
         }
         if (assertKeYVersions) {
            assertEquals(expected.getKeyVersion(), actual.getKeyVersion());
            assertEquals(expected.getKeyInternalVersion(), actual.getKeyInternalVersion());
         }
         assertFormInput(expected.getCurrentFormInput(), actual.getCurrentFormInput(), assertCurrentPage);
         assertFormInputs(expected.getFormInputs(), actual.getFormInputs(), assertCurrentPage);
      }
      else {
         assertNull(actual);
      }
   }

   /**
    * Ensures that the given {@link AbstractFormInput}s are equal.
    * @param expected The expected {@link AbstractFormInput}s.
    * @param actual The actual {@link AbstractFormInput}s.
    * @param assertCurrentPage Check current page?
    */
   public void assertFormInputs(AbstractFormInput<?>[] expected, AbstractFormInput<?>[] actual, boolean assertCurrentPage) {
      assertNotNull(expected);
      assertNotNull(actual);
      assertEquals(expected.length, actual.length);
      for (int i = 0; i < expected.length; i++) {
         assertFormInput(expected[i], actual[i], assertCurrentPage);
      }
   }

   /**
    * Ensures that the given {@link AbstractFormInput}s are equal.
    * @param expected The expected {@link AbstractFormInput}.
    * @param actual The actual {@link AbstractFormInput}.
    * @param assertCurrentPage Check current page?
    */
   public void assertFormInput(AbstractFormInput<?> expected, AbstractFormInput<?> actual, boolean assertCurrentPage) {
      if (expected != null) {
         assertNotNull(actual);
         assertNotSame(expected, actual);
         assertEquals(expected.getForm(), actual.getForm());
         if (assertCurrentPage) {
            assertPageInput(expected.getCurrentPageInput(), actual.getCurrentPageInput());
         }
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
   public void assertTools(RandomFormInput expected, RandomFormInput actual) {
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
   public void assertTool(Tool expected, Tool actual) {
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
   public void assertPageInputs(List<AbstractPageInput<?>> expected, List<AbstractPageInput<?>> actual) {
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
   public void assertPageInputs(AbstractPageInput<?>[] expected, AbstractPageInput<?>[] actual) {
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
   public void assertPageInput(AbstractPageInput<?> expected, AbstractPageInput<?> actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertNotSame(expected, actual);
         assertEquals(expected.getPage(), actual.getPage());
         assertEquals(expected.getShownTime(), actual.getShownTime());
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
         else if (expected instanceof InstructionPageInput) {
            assertTrue(actual instanceof InstructionPageInput);
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
   public void assertQuestionInputs(QuestionInput[] expected, QuestionInput[] actual) {
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
   public void assertQuestionInput(QuestionInput expected, QuestionInput actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertNotSame(expected, actual);
         assertEquals(expected.getQuestion(), actual.getQuestion());
         assertEquals(expected.getValue(), actual.getValue());
         assertEquals(expected.getValueSetAt(), actual.getValueSetAt());
         assertEquals(expected.getTrust(), actual.getTrust());
         assertEquals(expected.getTrustSetAt(), actual.getTrustSetAt());
         assertEquals(expected.hasChoiceInputs(), actual.hasChoiceInputs());
         if (expected.hasChoiceInputs()) {
            assertTrue(actual.hasChoiceInputs());
            for (Choice choice : expected.getChoices()) {
               assertQuestionInputs(expected.getChoiceInputs(choice), actual.getChoiceInputs(choice));
            }
         }
         else {
            assertFalse(actual.hasChoiceInputs());
         }
         assertEquals(expected.countChildInputs(), actual.countChildInputs());
         assertQuestionInputs(expected.getChildInputs(), actual.getChildInputs());
      }
      else {
         assertNull(actual);
      }
   }
   
   /**
    * Fills the given {@link EvaluationInput} completely with fixed values.
    * @param questionInput The {@link EvaluationInput} to fill.
    */
   public void fillEvaluationInput(EvaluationInput input) {
      input.setCurrentFormInput(input.getFormInput(input.countFormInputs() - 1));
      input.setUUID("A new UUID set by fillEvaluationInput");
      input.setTimestamp(System.currentTimeMillis());
      for (AbstractFormInput<?> formInput : input.getFormInputs()) {
         fillFormInput(formInput);
      }
   }

   /**
    * Fills the given {@link AbstractFormInput} completely with fixed values.
    * @param questionInput The {@link AbstractFormInput} to fill.
    */
   public void fillFormInput(AbstractFormInput<?> formInput) {
      formInput.setCurrentPageInput(formInput.getPageInput(formInput.countPageInputs() - 1));
      for (AbstractPageInput<?> pageInput : formInput.getPageInputs()) {
         fillPageInput(pageInput);
      }
      if (formInput instanceof FixedFormInput) {
         // Nothing to do
      }
      else if (formInput instanceof RandomFormInput) {
         RandomFormInput randomInput = (RandomFormInput) formInput;
         randomInput.setPageOrder(CollectionUtil.toList(formInput.getPageInputs()));
         Tool[] tools = formInput.getEvaluationInput().getEvaluation().getTools();
         if (tools.length > 0) {
            for (AbstractPageInput<?> page : formInput.getPageInputs()) {
               randomInput.setTool(page, tools[0]);
            }
         }
      }
      else {
         fail("Unsupported form input: " + formInput);
      }
   }

   /**
    * Fills the given {@link AbstractPageInput} completely with fixed values.
    * @param questionInput The {@link AbstractPageInput} to fill.
    */
   public void fillPageInput(AbstractPageInput<?> pageInput) {
      pageInput.setShownTime(4711);
      if (pageInput instanceof InstructionPageInput) {
         // Nothing to do
      }
      else if (pageInput instanceof QuestionPageInput) {
         QuestionPageInput qpi = (QuestionPageInput) pageInput;
         for (QuestionInput questionInput : qpi.getQuestionInputs()) {
            fillQuestionInput(questionInput);
         }
      }
      else if (pageInput instanceof SendFormPageInput) {
         SendFormPageInput sfpi = (SendFormPageInput) pageInput;
         sfpi.setSendingInProgress(true);
         fillQuestionInput(sfpi.getAcceptInput());
      }
      else if (pageInput instanceof ToolPageInput) {
         // Nothing to do
      }
      else {
         fail("Unsupported page input: " + pageInput);
      }
   }

   /**
    * Fills the given {@link QuestionInput} completely with fixed values.
    * @param questionInput The {@link QuestionInput} to fill.
    */
   public void fillQuestionInput(QuestionInput questionInput) {
      questionInput.setTrust(Trust.SURE);
      questionInput.setTrustSetAt(123);
      questionInput.setValue("A new value set by fillQuestionInput");
      questionInput.setValueSetAt(42);
      if (questionInput.hasChoiceInputs()) {
         for (Choice choice : questionInput.getChoices()) {
            for (QuestionInput choiceInput : questionInput.getChoiceInputs(choice)) {
               fillQuestionInput(choiceInput);
            }
         }
      }
      if (questionInput.countChildInputs() > 0) {
         for (QuestionInput childInput : questionInput.getChildInputs()) {
            fillQuestionInput(childInput);
         }
      }
   }
}
