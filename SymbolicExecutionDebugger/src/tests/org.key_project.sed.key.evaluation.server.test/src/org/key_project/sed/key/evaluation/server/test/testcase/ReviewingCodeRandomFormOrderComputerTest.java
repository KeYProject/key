package org.key_project.sed.key.evaluation.server.test.testcase;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.Entry;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.sed.key.evaluation.server.random.ReviewingCodeRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.server.random.ReviewingCodeRandomFormOrderComputer.BalancingEntry;
import org.key_project.sed.key.evaluation.server.random.ReviewingCodeRandomFormOrderComputer.IndexData;
import org.key_project.sed.key.evaluation.server.random.ReviewingCodeRandomFormOrderComputer.IndexEntryComparator;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IntegerUtil;

/**
 * Tests for {@link ReviewingCodeRandomFormOrderComputer}.
 * @author Martin Hentschel
 */
public class ReviewingCodeRandomFormOrderComputerTest extends TestCase {
   /**
    * If {@code true} intermediate states are printed into the console.
    */
   private static final boolean VERBOSE = false;
   
   /**
    * Tests the computed orders
    */
   @Test
   public void testComputeRandomValues() throws Exception{
      doComputeRandomValuesTest(IntegerUtil.factorial(6) * 10 + 1); // 10 iterations plus one additional iteration to trigger complete test
   }
   
   /**
    * Performs the test steps to test {@link ReviewingCodeRandomFormOrderComputer#computeRandomValues(EvaluationInput, AbstractFormInput)}
    * by applying multiple requests.
    * @param numberOfRequests The number of requests.
    * @throws Exception Occurred Exception.
    */
   protected void doComputeRandomValuesTest(int numberOfRequests) throws Exception{
      File storageLocation = IOUtil.createTempDirectory("ReviewingCodeRandomFormOrderComputer", "Test");
      try {
         ReviewingCodeRandomFormOrderComputer computer = new ReviewingCodeRandomFormOrderComputer(storageLocation);
         // Ensure right index content
         BalancingEntry balancingEntry = computer.getBalancingEntry();
         for (Entry<String, IndexData> entry : balancingEntry.getPermutationIndex().getIndex()) {
            assertIndexData(new IndexData(), entry.getData());
         }
         // Ensure right balancing content
         assertEquals(0, balancingEntry.getNoToolCountTotal());
         assertEquals(0, balancingEntry.getSedCountTotal());
         // Compute order
         assertNotNull(balancingEntry);
         boolean expectedNoToolFirst = false;
         int expectedNoToolTotalCount = 0;
         int expectedSedTotolCount = 0;
         assertEquals(expectedNoToolTotalCount, balancingEntry.getNoToolCountTotal());
         assertEquals(expectedSedTotolCount, balancingEntry.getSedCountTotal());
         Entry<String, IndexData> firstEntry = balancingEntry.getPermutationIndex().getIndex().get(0);
         EntryBackup firstEntryBackup = new EntryBackup(firstEntry);
         for (int i = 0; i < numberOfRequests; i++) {
            // Ensure that each permutation was updated twice once with NO_TOOL and once with NO_TOOL after enough requests
            if (i % (balancingEntry.getPermutationIndex().size() * 2) == 0) {
               int numOfCompleteIterations = i / (balancingEntry.getPermutationIndex().size() * 2);
               for (Entry<String, IndexData> entry : balancingEntry.getPermutationIndex().getIndex()) {
                  assertIndexData(new IndexData(numOfCompleteIterations, numOfCompleteIterations, 0, 0), entry.getData());
               }
               // Ensure right balancing content
               assertEquals(i / 2, balancingEntry.getNoToolCountTotal());
               assertEquals(i / 2, balancingEntry.getSedCountTotal());
            }
            // Compute order
            EvaluationInput evaluationInput = createDummyEvaluationInput();
            List<RandomFormInput> order = computer.computeRandomValues(evaluationInput, evaluationInput.getCurrentFormInput());
            if (VERBOSE) {
               System.out.println(firstEntryBackup + " changed to " + new EntryBackup(firstEntry));
            }
            assertRandomOrder(order, expectedNoToolFirst, firstEntryBackup.getPermutation());
            // Test counts
            if (expectedNoToolFirst) {
               expectedNoToolTotalCount++;
               assertEquals(firstEntryBackup.getNoToolCount() + 1, firstEntry.getData().getNoToolCount());
               assertEquals(firstEntryBackup.getSedCount(), firstEntry.getData().getSedCount());
            }
            else {
               expectedSedTotolCount++;
               assertEquals(firstEntryBackup.getNoToolCount(), firstEntry.getData().getNoToolCount());
               assertEquals(firstEntryBackup.getSedCount() + 1, firstEntry.getData().getSedCount());
            }
            assertEquals(0, firstEntry.getData().getNoToolCompletedCount());
            assertEquals(0, firstEntry.getData().getSedCompletedCount());
            assertEquals(expectedNoToolTotalCount, balancingEntry.getNoToolCountTotal());
            assertEquals(expectedSedTotolCount, balancingEntry.getSedCountTotal());
            // Compute new expected values for next loop iteration.
            expectedNoToolFirst = !expectedNoToolFirst;
            if (i % 2 == 1) { // The expected first entry changes only each 2 iterations
               ReviewingCodeRandomFormOrderComputer.BalancingEntryUpdater updater = new ReviewingCodeRandomFormOrderComputer.BalancingEntryUpdater(balancingEntry);
               firstEntry = updater.searchEntryToModify(balancingEntry.getPermutationIndex().getIndex());
            }
            firstEntryBackup = new EntryBackup(firstEntry);
         }
         if (VERBOSE) {
            System.out.println();
            balancingEntry.getPermutationIndex().print();
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
       * The NO_TOOL count value.
       */
      private final int noToolCount;
      
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
         noToolCount = entry.getData().getNoToolCount();
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
       * Returns the NO_TOOL count value.
       * @return The NO_TOOL count value.
       */
      public int getNoToolCount() {
         return noToolCount;
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
         return "(" + ArrayUtil.toString(permutation) + ": NO_TOOL = " + noToolCount + ", SED = " + sedCount + ")";
      }
   }
   
   /**
    * Ensures that the given {@link RandomFormInput}s have the right order.
    * @param actualRandomOrders The actual {@link RandomFormInput}s.
    * @param expectedNoToolFirst {@code true} NO_TOOL first, {@code false} SED first.
    * @param expectedCroofOrder The expected proof order.
    */
   protected void assertRandomOrder(List<RandomFormInput> actualRandomOrders, boolean expectedNoToolFirst, String... expectedCroofOrder) {
      assertNotNull(actualRandomOrders);
      assertEquals(1, actualRandomOrders.size());
      RandomFormInput actualFormInput = actualRandomOrders.get(0);
      // Ensure right form
      assertEquals(ReviewingCodeEvaluation.EVALUATION_FORM_NAME, actualFormInput.getForm().getName());
      int expectedIndex = 0;
      // Ensure right order
      for (AbstractPageInput<?> actualPageInput : actualFormInput.getPageOrder()) {
         if (isExamplePage(actualPageInput)) {
            assertEquals(expectedCroofOrder[expectedIndex], actualPageInput.getPage().getName());
            // Ensure right tools
            Tool tool = actualFormInput.getTool(actualPageInput);
            assertNotNull(tool);
            if (expectedNoToolFirst) {
               if (expectedIndex < 3) {
                  assertEquals(ReviewingCodeEvaluation.NO_TOOL_NAME, tool.getName());
               }
               else {
                  assertEquals(ReviewingCodeEvaluation.SED_TOOL_NAME, tool.getName());
               }
            }
            else {
               if (expectedIndex < 3) {
                  assertEquals(ReviewingCodeEvaluation.SED_TOOL_NAME, tool.getName());
               }
               else {
                  assertEquals(ReviewingCodeEvaluation.NO_TOOL_NAME, tool.getName());
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
   protected boolean isExamplePage(AbstractPageInput<?> input) {
      String name = input.getPage().getName();
      return ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME.equals(name) ||
             ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME.equals(name) ||
             ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME.equals(name) ||
             ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME.equals(name) ||
             ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME.equals(name) ||
             ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME.equals(name);
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
    * Tests the initial {@link PermutationIndex} created by {@link ReviewingCodeRandomFormOrderComputer#ReviewingCodeRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_NoData() throws Exception {
      Map<String, IndexData> expectedData = new HashMap<String,IndexData>();
      doInitialIndexTest(expectedData);
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link ReviewingCodeRandomFormOrderComputer#ReviewingCodeRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleIncompleteNoTool() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME), 
                   new IndexData(1, 0, 0, 0));
      doInitialIndexTest(noneData,
                         new IntroductionFormInputFileCreator(true, false, false));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link ReviewingCodeRandomFormOrderComputer#ReviewingCodeRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleIncompleteSED() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME), 
                   new IndexData(0, 1, 0, 0));
      doInitialIndexTest(noneData,
                         new IntroductionFormInputFileCreator(false, false, false));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link ReviewingCodeRandomFormOrderComputer#ReviewingCodeRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleNoTool() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME), 
                   new IndexData(1, 0, 1, 0));
      doInitialIndexTest(noneData,
                         new IntroductionFormInputFileCreator(true, false, true));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link ReviewingCodeRandomFormOrderComputer#ReviewingCodeRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleSED() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME), 
                                      new IndexData(0, 1, 0, 1));
      doInitialIndexTest(noneData,
                         new IntroductionFormInputFileCreator(false, false, true));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link ReviewingCodeRandomFormOrderComputer#ReviewingCodeRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_Multile() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME), 
                   new IndexData(2, 2, 1, 1));
      noneData.put(ArrayUtil.toString(ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME, 
                                      ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME), 
                   new IndexData(2, 2, 1, 1));
      doInitialIndexTest(noneData,
                         new IntroductionFormInputFileCreator(false, false, false),
                         new IntroductionFormInputFileCreator(false, false, true),
                         new IntroductionFormInputFileCreator(false, true, false),
                         new IntroductionFormInputFileCreator(false, true, true),
                         new IntroductionFormInputFileCreator(true, false, false),
                         new IntroductionFormInputFileCreator(true, false, true),
                         new IntroductionFormInputFileCreator(true, true, false),
                         new IntroductionFormInputFileCreator(true, true, true));
   }
   
   /**
    * Performs the test steps to test the initial {@link PermutationIndex} created by {@link ReviewingCodeRandomFormOrderComputer#ReviewingCodeRandomFormOrderComputer(File)}.
    * @param expectedData The expected {@link IndexData}.
    * @param creators {@link IFormInputFileCreator} to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doInitialIndexTest(Map<String, IndexData> expectedIndexData, 
                                     IFormInputFileCreator... creators) throws Exception {
      assertNotNull(expectedIndexData);
      File storageLocation = IOUtil.createTempDirectory("ReviewingCodeRandomFormOrderComputer", "Test");
      try {
         for (IFormInputFileCreator creator : creators) {
            creator.createFormInputFile(storageLocation);
         }
         ReviewingCodeRandomFormOrderComputer computer = new ReviewingCodeRandomFormOrderComputer(storageLocation);
         // Ensure right index content
         BalancingEntry balancingEntry = computer.getBalancingEntry();
         int noToolCountTotal = 0;
         int sedCountTotal = 0;
         for (Entry<String, IndexData> entry : balancingEntry.getPermutationIndex().getIndex()) {
            if (expectedIndexData != null) {
               String permuationKey = ArrayUtil.toString(entry.getPermutation());
               IndexData expected = expectedIndexData.get(permuationKey);
               if (expected != null) {
                  noToolCountTotal += expected.getNoToolCount();
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
         assertEquals(noToolCountTotal, balancingEntry.getNoToolCountTotal());
         assertEquals(sedCountTotal, balancingEntry.getSedCountTotal());
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
       * NO_TOOL first?
       */
      private final boolean noToolFirst;
      
      /**
       * Reverse order?
       */
      private final boolean reverseOrder;
      
      /**
       * Is the evaluation input completed?
       */
      private final boolean completed;
      
      /**
       * Constructor.
       * @param noToolFirst NO_TOOL first?
       * @param reverseOrder Reverse order?
       * @param completed Is the evaluation input completed?
       */
      public IntroductionFormInputFileCreator(boolean noToolFirst, boolean reverseOrder, boolean completed) {
         this.noToolFirst = noToolFirst;
         this.reverseOrder = reverseOrder;
         this.completed = completed;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createFormInputFile(File storageLocation) throws Exception {
         EvaluationInput evaluationInput = createDummyEvaluationInput();
         AbstractFormInput<?> introductionFormInput = evaluationInput.getCurrentFormInput();
         List<RandomFormInput> updatedOrders = ReviewingCodeRandomFormOrderComputer.computeFixedOrder(evaluationInput, introductionFormInput, noToolFirst, reverseOrder);
         FileStorage.store(storageLocation, introductionFormInput, updatedOrders);
         if (completed) {
            AbstractFormInput<?> evaluationFormInput = evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(ReviewingCodeEvaluation.EVALUATION_FORM_NAME));
            evaluationInput.setCurrentFormInput(evaluationFormInput);
            FileStorage.store(storageLocation, evaluationFormInput, null);
         }
      }
   }
   
   /**
    * Creates a dummy {@link EvaluationInput} on which the current form is the introduction form.
    * @return The created {@link EvaluationInput}.
    */
   protected static EvaluationInput createDummyEvaluationInput() {
      EvaluationInput evaluationInput = new EvaluationInput(ReviewingCodeEvaluation.INSTANCE);
      AbstractFormInput<?> introductionFormInput = evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(ReviewingCodeEvaluation.INTRODUCTION_FORM_NAME));
      evaluationInput.setCurrentFormInput(introductionFormInput);
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
      assertEquals(expected.getNoToolCount(), actual.getNoToolCount());
      assertEquals(expected.getNoToolCompletedCount(), actual.getNoToolCompletedCount());
      assertEquals(expected.getSedCount(), actual.getSedCount());
      assertEquals(expected.getSedCompletedCount(), actual.getSedCompletedCount());
   }

   /**
    * Tests {@link ReviewingCodeRandomFormOrderComputer#isToolUsedFirst(java.util.List, String, String)}.
    */
   @Test
   public void testIsToolUsedFirst() {
      // Get tools
      Tool noTool = new Tool("noTool", null, null, null);
      Tool sed = new Tool("sed", null, null, null);
      Tool invalid = new Tool("invalidTool", null, null, null);
      // Perform tests
      assertTrue(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(noTool, noTool, noTool, sed, sed, sed), noTool.getName(), sed.getName(), 6));
      assertFalse(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(sed, sed, sed, noTool, noTool, noTool), noTool.getName(), sed.getName(), 6));
      assertFalse(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(noTool, sed, noTool, sed, noTool, sed), noTool.getName(), sed.getName(), 6));
      assertFalse(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(invalid, noTool, noTool, sed, sed, sed), noTool.getName(), sed.getName(), 6));
      assertFalse(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(noTool, noTool, invalid, sed, sed, sed), noTool.getName(), sed.getName(), 6));
      assertFalse(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(noTool, noTool, noTool, invalid, sed, sed), noTool.getName(), sed.getName(), 6));
      assertFalse(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(noTool, noTool, noTool, sed, sed, invalid), noTool.getName(), sed.getName(), 6));
      assertFalse(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(noTool, noTool, noTool, sed, sed), noTool.getName(), sed.getName(), 6));
      assertFalse(ReviewingCodeRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(noTool, noTool, noTool, sed, sed, sed, sed), noTool.getName(), sed.getName(), 6));
   }
}
