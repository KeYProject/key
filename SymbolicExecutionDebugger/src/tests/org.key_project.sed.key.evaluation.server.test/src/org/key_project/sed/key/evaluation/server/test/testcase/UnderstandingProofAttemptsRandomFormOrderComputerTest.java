package org.key_project.sed.key.evaluation.server.test.testcase;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.Entry;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer.BalancingEntry;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer.IndexData;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer.IndexEntryComparator;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IntegerUtil;

/**
 * Tests for {@link UnderstandingProofAttemptsRandomFormOrderComputer}.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsRandomFormOrderComputerTest extends TestCase {
   /**
    * If {@code true} intermediate states are printed into the console.
    */
   private static final boolean VERBOSE = false;
   
   /**
    * Tests the computed orders
    */
   @Test
   public void testComputeRandomValues() throws Exception{
      doComputeRandomValuesTest(IntegerUtil.factorial(4) * 10 + 1); // 10 iterations plus one additional iteration to trigger complete test
   }
   
   /**
    * Performs the test steps to test {@link UnderstandingProofAttemptsRandomFormOrderComputer#computeRandomValues(EvaluationInput, AbstractFormInput)}
    * by applying multiple requests.
    * @param numberOfRequests The number of requests.
    * @throws Exception Occurred Exception.
    */
   protected void doComputeRandomValuesTest(int numberOfRequests) throws Exception{
      File storageLocation = IOUtil.createTempDirectory("UnderstandingProofAttemptsRandomFormOrderComputer", "Test");
      try {
         UnderstandingProofAttemptsRandomFormOrderComputer computer = new UnderstandingProofAttemptsRandomFormOrderComputer(storageLocation);
         // Ensure that all expected indices exist
         AbstractForm introductionForm = UnderstandingProofAttemptsEvaluation.INSTANCE.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
         QuestionPage backgroundPage = (QuestionPage) introductionForm.getPage(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
         RadioButtonsQuestion keyQuestion = (RadioButtonsQuestion) backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
         assertEquals(keyQuestion.countChoices(), computer.getBalancingMap().size());
         for (Choice choice : keyQuestion.getChoices()) {
            assertTrue(computer.getBalancingMap().containsKey(choice.getValue()));
            // Ensure right index content
            BalancingEntry balancingEntry = computer.getBalancingEntry(choice.getValue());
            for (Entry<String, IndexData> entry : balancingEntry.getPermutationIndex().getIndex()) {
               assertIndexData(new IndexData(), entry.getData());
            }
            // Ensure right balancing content
            assertEquals(0, balancingEntry.getKeyCountTotal());
            assertEquals(0, balancingEntry.getSedCountTotal());
         }
         // Compute order
         BalancingEntry nonBalancingEntry = computer.getBalancingMap().get(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE);
         assertNotNull(nonBalancingEntry);
         boolean expectedKeYFirst = false;
         int expectedKeYTotalCount = 0;
         int expectedSedTotolCount = 0;
         assertEquals(expectedKeYTotalCount, nonBalancingEntry.getKeyCountTotal());
         assertEquals(expectedSedTotolCount, nonBalancingEntry.getSedCountTotal());
         Entry<String, IndexData> firstEntry = nonBalancingEntry.getPermutationIndex().getIndex().get(0);
         EntryBackup firstEntryBackup = new EntryBackup(firstEntry);
         for (int i = 0; i < numberOfRequests; i++) {
            // Ensure that each permutation was updated twice once with KeY and once with KeY after enough requests
            if (i % (nonBalancingEntry.getPermutationIndex().size() * 2) == 0) {
               int numOfCompleteIterations = i / (nonBalancingEntry.getPermutationIndex().size() * 2);
               for (Entry<String, IndexData> entry : nonBalancingEntry.getPermutationIndex().getIndex()) {
                  assertIndexData(new IndexData(numOfCompleteIterations, numOfCompleteIterations, 0, 0), entry.getData());
               }
               // Ensure right balancing content
               assertEquals(i / 2, nonBalancingEntry.getKeyCountTotal());
               assertEquals(i / 2, nonBalancingEntry.getSedCountTotal());
            }
            // Compute order
            EvaluationInput evaluationInput = createDummyEvaluationInput(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE);
            List<RandomFormInput> order = computer.computeRandomValues(evaluationInput, evaluationInput.getCurrentFormInput());
            if (VERBOSE) {
               System.out.println(firstEntryBackup + " changed to " + new EntryBackup(firstEntry));
            }
            assertRandomOrder(order, expectedKeYFirst, firstEntryBackup.getPermutation());
            // Test counts
            if (expectedKeYFirst) {
               expectedKeYTotalCount++;
               assertEquals(firstEntryBackup.getKeyCount() + 1, firstEntry.getData().getKeyCount());
               assertEquals(firstEntryBackup.getSedCount(), firstEntry.getData().getSedCount());
            }
            else {
               expectedSedTotolCount++;
               assertEquals(firstEntryBackup.getKeyCount(), firstEntry.getData().getKeyCount());
               assertEquals(firstEntryBackup.getSedCount() + 1, firstEntry.getData().getSedCount());
            }
            assertEquals(0, firstEntry.getData().getKeyCompletedCount());
            assertEquals(0, firstEntry.getData().getSedCompletedCount());
            assertEquals(expectedKeYTotalCount, nonBalancingEntry.getKeyCountTotal());
            assertEquals(expectedSedTotolCount, nonBalancingEntry.getSedCountTotal());
            // Ensure that other indicies have still the initial state
            for (Choice choice : keyQuestion.getChoices()) {
               // Ensure right index content
               BalancingEntry balancingEntry = computer.getBalancingEntry(choice.getValue());
               if (balancingEntry != nonBalancingEntry) {
                  for (Entry<String, IndexData> entry : balancingEntry.getPermutationIndex().getIndex()) {
                     assertIndexData(new IndexData(), entry.getData());
                  }
                  // Ensure right balancing content
                  assertEquals(0, balancingEntry.getKeyCountTotal());
                  assertEquals(0, balancingEntry.getSedCountTotal());
               }
            }
            // Compute new expected values for next loop iteration.
            expectedKeYFirst = !expectedKeYFirst;
            if (i % 2 == 1) { // The expected first entry changes only each 2 iterations
               firstEntry = nonBalancingEntry.getPermutationIndex().getIndex().get(0);
            }
            firstEntryBackup = new EntryBackup(firstEntry);
         }
         if (VERBOSE) {
            System.out.println();
            nonBalancingEntry.getPermutationIndex().print();
         }
      }
      finally {
         IOUtil.delete(storageLocation);
      }
   }
   
   /**
    * Helper class to store the content of an {@link Entry}.
    * @author Martin Hentschel
    */
   protected static class EntryBackup {
      /**
       * The permutation.
       */
      private final String[] permutation;
      
      /**
       * The KeY count value.
       */
      private final int keyCount;
      
      /**
       * The SED count value.
       */
      private final int sedCount;

      /**
       * Constructor.
       * @param entry The {@link Entry} to backup.
       */
      public EntryBackup(Entry<String, IndexData> entry) {
         permutation = entry.getPermutation();
         keyCount = entry.getData().getKeyCount();
         sedCount = entry.getData().getSedCount();
      }

      /**
       * Returns the permutation.
       * @return The permutation.
       */
      public String[] getPermutation() {
         return permutation;
      }

      /**
       * Returns the KeY count value.
       * @return The KeY count value.
       */
      public int getKeyCount() {
         return keyCount;
      }

      /**
       * Returns the SED count value.
       * @return The SED count value.
       */
      public int getSedCount() {
         return sedCount;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return "(" + ArrayUtil.toString(permutation) + ": KeY = " + keyCount + ", SED = " + sedCount + ")";
      }
   }
   
   /**
    * Ensures that the given {@link RandomFormInput}s have the right order.
    * @param actualRandomOrders The actual {@link RandomFormInput}s.
    * @param expectedKeYFirst {@code true} KeY first, {@code false} SED first.
    * @param expectedCroofOrder The expected proof order.
    */
   protected void assertRandomOrder(List<RandomFormInput> actualRandomOrders, boolean expectedKeYFirst, String... expectedCroofOrder) {
      assertNotNull(actualRandomOrders);
      assertEquals(1, actualRandomOrders.size());
      RandomFormInput actualFormInput = actualRandomOrders.get(0);
      // Ensure right form
      assertEquals(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME, actualFormInput.getForm().getName());
      int expectedIndex = 0;
      // Ensure right order
      for (AbstractPageInput<?> actualPageInput : actualFormInput.getPageOrder()) {
         if (isProofPage(actualPageInput)) {
            assertEquals(expectedCroofOrder[expectedIndex], actualPageInput.getPage().getName());
            // Ensure right tools
            Tool tool = actualFormInput.getTool(actualPageInput);
            assertNotNull(tool);
            if (expectedKeYFirst) {
               if (expectedIndex < 2) {
                  assertEquals(UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME, tool.getName());
               }
               else {
                  assertEquals(UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME, tool.getName());
               }
            }
            else {
               if (expectedIndex < 2) {
                  assertEquals(UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME, tool.getName());
               }
               else {
                  assertEquals(UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME, tool.getName());
               }
            }
            expectedIndex++;
         }
      }
   }
   
   /**
    * Checks if the given {@link AbstractPageInput} is a proof page.
    * @param input The {@link AbstractFormInput} to check.
    * @return {@code true} is proof page, {@code false} is something else.
    */
   protected boolean isProofPage(AbstractPageInput<?> input) {
      String name = input.getPage().getName();
      return UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME.equals(name) ||
             UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME.equals(name) ||
             UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME.equals(name) ||
             UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME.equals(name);
   }
   
   /**
    * Tests {@link IndexEntryComparator}.
    */
   @Test
   public void testIndexDataComparator() {
      // Test equal instances
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 0, 0, 0), 0);
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(1, 0, 0, 0), 0);
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(0, 2, 0, 0), 0);
      doComparisionTest(new IndexData(0, 0, 3, 0), new IndexData(0, 0, 3, 0), 0);
      doComparisionTest(new IndexData(0, 0, 0, 4), new IndexData(0, 0, 0, 4), 0);
      // Test random examples
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 0, 0, 0), 1); // Second smaller, because other tool is missing
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 1, 0, 0), 1); // Second smaller, because other tool is missing
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 1, 0, 0), -1); // First smaller, because less used
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(0, 2, 0, 0), -1); // First smaller, because less used
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(0, 2, 0, 0), -1); // First smaller, because less used
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 2, 0, 0), -1); // First smaller, because less used
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 1, 0, 0), 1); // Second smaller, because other tool is missing
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(3, 1, 0, 0), 1); // Second smaller, because other tool is missing
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(3, 1, 0, 0), -1); // First smaller, because less used
      // Test different counts systematically
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 0, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 2, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(2, 1, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller

      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(0, 1, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(0, 2, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(1, 0, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(1, 2, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(2, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(2, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(0, 2, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(1, 2, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(2, 0, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(2, 1, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(0, 1, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(0, 2, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(1, 0, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(1, 2, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(2, 0, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(2, 1, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(0, 0, 0, 0), 1); // Bigger
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(1, 1, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(1, 2, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 1, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller

      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger as less unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(1, 2, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as less unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(2, 1, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(0, 2, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(1, 2, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(2, 0, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(2, 1, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(1, 2, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(2, 1, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(0, 0, 0, 0), 1); // Bigger
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(1, 1, 0, 0), 1); // Bigger balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(1, 2, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(2, 1, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(2, 2, 0, 0), 0); // Equal
   }
   
   /**
    * Compares the given {@link IndexData} using an {@link IndexEntryComparator}.
    * The comparison is also performed in reverse order.
    * @param first The first {@link IndexData}.
    * @param second The second {@link IndexData}.
    * @param expectedOutcome The expected outcome.
    */
   protected void doComparisionTest(IndexData first, IndexData second, int expectedOutcome) {
      Entry<String, IndexData> firstEntry = new Entry<String, IndexData>(new String[] {"first"}, first);
      Entry<String, IndexData> secondEntry = new Entry<String, IndexData>(new String[] {"second"}, second);
      IndexEntryComparator c = new IndexEntryComparator();
      assertEquals(expectedOutcome, c.compare(firstEntry, secondEntry));
      assertEquals(expectedOutcome * -1, c.compare(secondEntry, firstEntry)); // Test reverse order
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_NoData() throws Exception {
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      doInitialIndexTest(expectedData);
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleIncompleteKeY() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(1, 0, 0, 0));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(true, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleIncompleteSED() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(0, 1, 0, 0));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(false, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleKeY() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(1, 0, 1, 0));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(true, false, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleSED() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(0, 1, 0, 1));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(false, false, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_Multile() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(2, 2, 1, 1));
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME), 
                   new IndexData(2, 2, 1, 1));
      Map<String, IndexData> lessData = new HashMap<String, IndexData>();
      lessData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(1, 0, 0, 0));
      Map<String, IndexData> moreData = new HashMap<String, IndexData>();
      moreData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(1, 1, 0, 0));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE, lessData);
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE, moreData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(false, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(false, false, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(false, true, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(false, true, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, false, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, true, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, true, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE),
                         new IntroductionFormInputFileCreator(true, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE),
                         new IntroductionFormInputFileCreator(false, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE));
   }
   
   /**
    * Performs the test steps to test the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @param expectedData The expected {@link IndexData}.
    * @param creators {@link IFormInputFileCreator} to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doInitialIndexTest(final Map<String, Map<String, IndexData>> expectedData, 
                                     IFormInputFileCreator... creators) throws Exception {
      assertNotNull(expectedData);
      File storageLocation = IOUtil.createTempDirectory("UnderstandingProofAttemptsRandomFormOrderComputer", "Test");
      try {
         for (IFormInputFileCreator creator : creators) {
            creator.createFormInputFile(storageLocation);
         }
         UnderstandingProofAttemptsRandomFormOrderComputer computer = new UnderstandingProofAttemptsRandomFormOrderComputer(storageLocation);
         // Ensure that all expected indices exist
         AbstractForm introductionForm = UnderstandingProofAttemptsEvaluation.INSTANCE.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
         QuestionPage backgroundPage = (QuestionPage) introductionForm.getPage(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
         RadioButtonsQuestion keyQuestion = (RadioButtonsQuestion) backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
         assertEquals(keyQuestion.countChoices(), computer.getBalancingMap().size());
         for (Choice choice : keyQuestion.getChoices()) {
            assertTrue(computer.getBalancingMap().containsKey(choice.getValue()));
            // Ensure right index content
            Map<String, IndexData> expectedIndexData = expectedData.get(choice.getValue());
            BalancingEntry balancingEntry = computer.getBalancingEntry(choice.getValue());
            int keyCountTotal = 0;
            int sedCountTotal = 0;
            for (Entry<String, IndexData> entry : balancingEntry.getPermutationIndex().getIndex()) {
               if (expectedIndexData != null) {
                  String permuationKey = ArrayUtil.toString(entry.getPermutation());
                  IndexData expected = expectedIndexData.get(permuationKey);
                  if (expected != null) {
                     keyCountTotal += expected.getKeyCount();
                     sedCountTotal += expected.getSedCount();
                     assertIndexData(expected, entry.getData());
                  }
                  else {
                     assertIndexData(new IndexData(), entry.getData());
                  }
               }
               else {
                  assertIndexData(new IndexData(), entry.getData());
               }
            }
            // Ensure right balancing content
            assertEquals(keyCountTotal, balancingEntry.getKeyCountTotal());
            assertEquals(sedCountTotal, balancingEntry.getSedCountTotal());
         }
      }
      finally {
         IOUtil.delete(storageLocation);
      }
   }
   
   /**
    * Creates form input of the introduction form.
    * @author Martin Hentschel
    */
   protected static class IntroductionFormInputFileCreator implements IFormInputFileCreator {
      /**
       * KeY first?
       */
      private final boolean keyFirst;
      
      /**
       * Reverse order?
       */
      private final boolean reverseOrder;
      
      /**
       * Is the evaluation input completed?
       */
      private final boolean completed;
      
      /**
       * The experience with KeY.
       */
      private final String keyExperience;
      
      /**
       * Constructor.
       * @param keyFirst KeY first?
       * @param reverseOrder Reverse order?
       * @param completed Is the evaluation input completed?
       */
      public IntroductionFormInputFileCreator(boolean keyFirst, boolean reverseOrder, boolean completed, String keyExperience) {
         this.keyFirst = keyFirst;
         this.reverseOrder = reverseOrder;
         this.completed = completed;
         this.keyExperience = keyExperience;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createFormInputFile(File storageLocation) throws Exception {
         EvaluationInput evaluationInput = createDummyEvaluationInput(keyExperience);
         AbstractFormInput<?> introductionFormInput = evaluationInput.getCurrentFormInput();
         List<RandomFormInput> updatedOrders = UnderstandingProofAttemptsRandomFormOrderComputer.computeFixedOrder(evaluationInput, introductionFormInput, keyFirst, reverseOrder);
         FileStorage.store(storageLocation, introductionFormInput, updatedOrders);
         if (completed) {
            AbstractFormInput<?> evaluationFormInput = evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME));
            evaluationInput.setCurrentFormInput(evaluationFormInput);
            FileStorage.store(storageLocation, evaluationFormInput, null);
         }
      }
   }
   
   /**
    * Creates a dummy {@link EvaluationInput} on which the current form is the introduction form.
    * @param keyExperience The key experience to set.
    * @return The created {@link EvaluationInput}.
    */
   protected static EvaluationInput createDummyEvaluationInput(String keyExperience) {
      EvaluationInput evaluationInput = new EvaluationInput(UnderstandingProofAttemptsEvaluation.INSTANCE);
      AbstractFormInput<?> introductionFormInput = evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME));
      evaluationInput.setCurrentFormInput(introductionFormInput);
      QuestionPageInput backgroundPageInput = (QuestionPageInput)introductionFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
      introductionFormInput.setCurrentPageInput(backgroundPageInput);
      QuestionInput keyInput = backgroundPageInput.getQuestionInput(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
      keyInput.setValue(keyExperience);
      return evaluationInput;
   }
   
   /**
    * Instances are used to create form input files.
    * @author Martin Hentschel
    */
   protected static interface IFormInputFileCreator {
      /**
       * Creates a form input file.
       * @param storageLocation The storage location to save file at.
       * @throws Exception Occurred Exception.
       */
      public void createFormInputFile(File storageLocation) throws Exception;
   }
   
   /**
    * Ensures that the given {@link IndexData} instances are equal.
    * @param expected The expected {@link IndexData}.
    * @param actual The current {@link IndexData}.
    */
   protected void assertIndexData(IndexData expected, IndexData actual) {
      assertNotSame(expected, actual);
      assertEquals(expected.getKeyCount(), actual.getKeyCount());
      assertEquals(expected.getKeyCompletedCount(), actual.getKeyCompletedCount());
      assertEquals(expected.getSedCount(), actual.getSedCount());
      assertEquals(expected.getSedCompletedCount(), actual.getSedCompletedCount());
   }

   /**
    * Tests {@link UnderstandingProofAttemptsRandomFormOrderComputer#isToolUsedFirst(java.util.List, String, String)}.
    */
   @Test
   public void testIsToolUsedFirst() {
      // Get tools
      Tool key = new Tool("key", null, null, null);
      Tool sed = new Tool("sed", null, null, null);
      Tool invalid = new Tool("invalidTool", null, null, null);
      // Perform tests
      assertTrue(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, sed, sed), key.getName(), sed.getName(), 4));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(sed, sed, key, key), key.getName(), sed.getName(), 4));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, sed, key, sed), key.getName(), sed.getName(), 4));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(invalid, key, sed, sed), key.getName(), sed.getName(), 4));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, invalid, sed, sed), key.getName(), sed.getName(), 4));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, invalid, sed), key.getName(), sed.getName(), 4));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, sed, invalid), key.getName(), sed.getName(), 4));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, sed), key.getName(), sed.getName(), 4));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, sed, sed, sed), key.getName(), sed.getName(), 4));
   }
}
