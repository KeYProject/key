package org.key_project.sed.key.evaluation.server.test.testcase;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.Entry;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.IDataFactory;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.IEntryUpdater;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IntegerUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link PermutationIndex}.
 * @author Martin Hentschel
 */
public class PermutationIndexTest extends TestCase {
   /**
    * Performs parallel modifications on a {@link PermutationIndex}.
    */
   @Test
   public void testParallelDataManipulation_2() {
      doParallelDataManipulationTest(new String[] {"A", "B"}, 10, 1000);
   }
   
   /**
    * Performs parallel modifications on a {@link PermutationIndex}.
    */
   @Test
   public void testParallelDataManipulation_3() {
      doParallelDataManipulationTest(new String[] {"A", "B", "C"}, 10, 1000);
   }
   
   /**
    * Performs parallel modifications on a {@link PermutationIndex}.
    * @param elements The elements.
    * @param iterations The number of iterations.
    * @param numberOfThreads The number of parallel {@link Thread}s.
    */
   protected void doParallelDataManipulationTest(String[] elements, int iterations, int numberOfThreads) {
      assertTrue(iterations >= 1);
      assertTrue(numberOfThreads >= 1);
      // Create index
      final PermutationIndex<String, Counter> permutationIndex = doInitialCounterAsDataTest(elements);
      // Perform modifications
      for (int i = 0; i < iterations; i++) {
         // Create threads
         ModificationThread[] threads = new ModificationThread[numberOfThreads];
         for (int j = 0; j < threads.length; j++) {
            threads[j] = new ModificationThread(permutationIndex);
         }
         // Start threads
         for (int j = 0; j < threads.length; j++) {
            threads[j].start();
         }
         // Wait for threads
         for (int j = 0; j < threads.length; j++) {
            while (threads[j].isAlive()) {
               TestUtilsUtil.sleep(10);
            }
         }
         // Test index
         assertPermutationIndexContent(elements, permutationIndex);
         // Assert data values
         for (Entry<String, Counter> entry : permutationIndex.getIndex()) {
            assertEquals((i + 1) * numberOfThreads, entry.getData().getValue());
         }
      }
   }
   
   /**
    * Thread performed by {@link PermutationIndexTest#doParallelDataManipulationTest(String[], int, int)}.
    * @author Martin Hentschel
    */
   private static final class ModificationThread extends Thread {
      /**
       * The {@link PermutationIndex} to work with.
       */
      private final PermutationIndex<String, Counter> permutationIndex;
      
      /**
       * Constructor.
       * @param permutationIndex The {@link PermutationIndex} to work with.
       */
      public ModificationThread(PermutationIndex<String, Counter> permutationIndex) {
         this.permutationIndex = permutationIndex;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run() {
         for (int j = 0; j < permutationIndex.size(); j++) {
            CounterEntryUpdater<String> updater = new CounterEntryUpdater<String>();
            permutationIndex.updateFirstEntry(updater);
         }
      }
   }
   
   /**
    * Tests a manipulation and reindexing of the data.
    */
   @Test
   public void testDataManipulation_2() {
      String[] elements = {"A", "B"};
      doDataManipulationTest(elements, 5);
   }
   
   /**
    * Tests a manipulation and reindexing of the data.
    */
   @Test
   public void testDataManipulation_3() {
      String[] elements = {"A", "B", "C"};
      doDataManipulationTest(elements, 5);
   }
   
   /**
    * Performs a test in which each data {@link Counter} is increased.
    * @param elements The elements.
    * @param iterations The number of iterations.
    */
   protected void doDataManipulationTest(String[] elements, int iterations) {
      // Create index
      PermutationIndex<String, Counter> permutationIndex = doInitialCounterAsDataTest(elements);
      // Update index
      assertTrue(iterations >= 1);
      for (int i = 0; i < iterations; i++) {
         for (int j = 0; j < permutationIndex.size(); j++) {
            CounterEntryUpdater<String> updater = new CounterEntryUpdater<String>();
            permutationIndex.updateFirstEntry(updater);
            assertPermutationIndexContent(elements, permutationIndex);
            assertEquals(i + 1, updater.getModifiedEntry().getData().getValue());
         }
      }
      // Test resulting values
      for (Entry<String, Counter> entry : permutationIndex.getIndex()) {
         assertEquals(iterations, entry.getData().getValue());
      }
   }
   
   /**
    * Performs the test steps to test an initially created {@link PermutationIndex}
    * in which the data is a {@link Counter} instance.
    * @param elements The available elements.
    * @return The created {@link PermutationIndex}.
    */
   protected <E> PermutationIndex<E, Counter> doInitialCounterAsDataTest(E[] elements) {
      IDataFactory<E, Counter> dataFactory = new IDataFactory<E, Counter>() {
         @Override
         public Counter createData(E[] permutation) {
            return new Counter();
         }
      };
      Comparator<Entry<E, Counter>> entryComparator = new Comparator<Entry<E, Counter>>() {
         @Override
         public int compare(Entry<E, Counter> o1, Entry<E, Counter> o2) {
            return o1.getData().compareTo(o2.getData());
         }
      };
      return doInitialIndexTest(elements, dataFactory, entryComparator);
   }
   
   /**
    * An {@link IEntryUpdater} which calls {@link Counter#increase()}
    * @author Martin Hentschel
    */
   protected static final class CounterEntryUpdater<E> implements IEntryUpdater<E, Counter> {
      /**
       * The modified first {@link Counter} entry.
       */
      private Entry<E, Counter> modifiedEntry;

      /**
       * {@inheritDoc}
       */
      @Override
      public Entry<E, Counter> updateEntry(List<Entry<E, Counter>> list) {
         Entry<E, Counter> firstEntry = list.get(0);
         assertNull(this.modifiedEntry);
         assertNotNull(firstEntry);
         firstEntry.getData().increase();
         this.modifiedEntry = firstEntry;
         return firstEntry;
      }

      /**
       * Returns the modified first {@link Counter} entry.
       * @return The modified first {@link Counter} entry.
       */
      public Entry<E, Counter> getModifiedEntry() {
         return modifiedEntry;
      }
   }
   
   /**
    * A {@link Counter}.
    * @author Martin Hentschel
    */
   protected static final class Counter implements Comparable<Counter> {
      /**
       * The value.
       */
      private int value;

      /**
       * Returns the value.
       * @return The returned value.
       */
      public int getValue() {
         return value;
      }

      /**
       * Increases the counter by {@code 1}.
       */
      public synchronized void increase() {
         value++;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int compareTo(Counter o) {
         return value - o.value;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int hashCode() {
         return value;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if (obj == this) {
            return true;
         }
         else if(obj == null || obj.getClass() != getClass() || hashCode() != obj.hashCode()) {
            return false; 
         }
         else {
            return value == ((Counter) obj).value;
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return value + "";
      }
   }
   
   /**
    * Tests a created {@link PermutationIndex}.
    */
   @Test
   public void testInitialIndex_length2() {
      doInitialPermutationAsDataTest(new String[] {"A", "B"});
   }

   /**
    * Tests a created {@link PermutationIndex}.
    */
   @Test
   public void testInitialIndex_length3() {
      doInitialPermutationAsDataTest(new String[] {"A", "B", "C"});
   }
   
   /**
    * Performs the test steps to test an initially created {@link PermutationIndex}
    * in which the data is the permutation.
    * @param elements The available elements.
    * @return The created {@link PermutationIndex}.
    */
   protected <E> PermutationIndex<E, String> doInitialPermutationAsDataTest(E[] elements) {
      IDataFactory<E, String> dataFactory = new IDataFactory<E, String>() {
         @Override
         public String createData(E[] permutation) {
            return ArrayUtil.toString(permutation);
         }
      };
      Comparator<Entry<E, String>> entryComparator = new Comparator<Entry<E, String>>() {
         @Override
         public int compare(Entry<E, String> o1, Entry<E, String> o2) {
            return o1.getData().compareTo(o2.getData());
         }
      };
      return doInitialIndexTest(elements, dataFactory, entryComparator);
   }
   
   /**
    * Performs the test steps to test an initially created {@link PermutationIndex}.
    * @param elements The available elements.
    * @return The created {@link PermutationIndex}.
    */
   protected <E, D> PermutationIndex<E, D> doInitialIndexTest(E[] elements, IDataFactory<E, D> dataFactory, Comparator<Entry<E, D>> dataComparator) {
      // Create index
      PermutationIndex<E, D> permutationIndex = new PermutationIndex<E, D>(elements, dataFactory, dataComparator);
      List<Entry<E, D>> index = permutationIndex.getIndex();
      // Test created index
      assertSame(dataComparator, permutationIndex.getEntryComparator());
      for (Entry<E, D> entry : index) {
         assertEquals(dataFactory.createData(entry.getPermutation()), entry.getData());
      }
      return permutationIndex;
   }
   
   /**
    * Ensures that
    * <ol>
    *    <li>All permutations of the given elements are contained in the index.</li>
    *    <li>Ensures that index is correctly sorted</li>
    * </ol>
    * @param elements The indexed elements.
    * @param permutationIndex The {@link PermutationIndex} to test.
    */
   protected <E, D> void assertPermutationIndexContent(E[] elements, PermutationIndex<E, D> permutationIndex) {
      List<Entry<E, D>> index = permutationIndex.getIndex();
      Comparator<Entry<E, D>> entryComparator = permutationIndex.getEntryComparator();
      // Test elements
      E[][] permutations = ArrayUtil.generatePermutations(elements);
      assertEquals(IntegerUtil.factorial(elements.length), index.size());
      assertEquals(permutations.length, index.size());
      // Ensure that all permutations are contained in index with correct data and order
      Set<String> remainingPermutations = new HashSet<String>();
      for (E[] permutation : permutations) {
         assertTrue(remainingPermutations.add(ArrayUtil.toString(permutation)));
      }
      Entry<E, D> previousEntry = null;
      for (Entry<E, D> entry : index) {
         if (previousEntry != null) {
            assertTrue(entryComparator.compare(previousEntry, entry) <= 0);
         }
         assertTrue(remainingPermutations.remove(ArrayUtil.toString(entry.getPermutation())));
         previousEntry = entry;
      }
   }
}
