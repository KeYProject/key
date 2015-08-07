package org.key_project.sed.key.evaluation.server.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.key.evaluation.server.random.AbstractRandomCompletion;

/**
 * Tests for {@link AbstractRandomCompletion}
 * @author Martin Hentschel
 */
public class AbstractRandomCompletionTest extends TestCase {
   /**
    * Tests {@link AbstractRandomCompletion#computePermutationDifference(String[], String[])}.
    */
   @Test
   public void testComputePermutationDifference() {
      // Permutations of length 2
      assertEquals(0, AbstractRandomCompletion.computePermutationDifference(new String[] {"A", "B"}, new String[] {"A", "B"}));
      assertEquals(2, AbstractRandomCompletion.computePermutationDifference(new String[] {"A", "B"}, new String[] {"B", "A"}));
      assertEquals(2, AbstractRandomCompletion.computePermutationDifference(new String[] {"B", "A"}, new String[] {"A", "B"}));
      // Permutations of length 3
      assertEquals(0, AbstractRandomCompletion.computePermutationDifference(new String[] {"A", "B", "C"}, new String[] {"A", "B", "C"}));
      assertEquals(2, AbstractRandomCompletion.computePermutationDifference(new String[] {"A", "B", "C"}, new String[] {"B", "A", "C"}));
      assertEquals(4, AbstractRandomCompletion.computePermutationDifference(new String[] {"A", "B", "C"}, new String[] {"C", "B", "A"}));
      assertEquals(4, AbstractRandomCompletion.computePermutationDifference(new String[] {"A", "B", "C"}, new String[] {"B", "C", "A"}));
      assertEquals(4, AbstractRandomCompletion.computePermutationDifference(new String[] {"A", "B", "C"}, new String[] {"C", "A", "B"}));
      assertEquals(2, AbstractRandomCompletion.computePermutationDifference(new String[] {"A", "B", "C"}, new String[] {"A", "C", "B"}));
      // Test relations of length 6
      int first = AbstractRandomCompletion.computePermutationDifference(new String[] {"MathUtil", "IntegerUtil", "BankUtil", "ObservableArray", "Stack", "ValueSearch"}, new String[] {"ValueSearch", "MathUtil", "Stack", "ObservableArray", "BankUtil", "IntegerUtil"});
      int second = AbstractRandomCompletion.computePermutationDifference(new String[] {"IntegerUtil", "ObservableArray", "BankUtil", "MathUtil", "ValueSearch", "Stack"}, new String[] {"ValueSearch", "MathUtil", "Stack", "ObservableArray", "BankUtil", "IntegerUtil"});
      assertTrue(first + " < " + second + " does not hold.", first < second);
      first = AbstractRandomCompletion.computePermutationDifference(new String[] {"MathUtil", "IntegerUtil", "BankUtil", "ObservableArray", "Stack", "ValueSearch"}, new String[] {"IntegerUtil", "BankUtil", "ObservableArray", "MathUtil", "ValueSearch", "Stack"});
      second = AbstractRandomCompletion.computePermutationDifference(new String[] {"IntegerUtil", "ObservableArray", "BankUtil", "MathUtil", "ValueSearch", "Stack"}, new String[] {"IntegerUtil", "BankUtil", "ObservableArray", "MathUtil", "ValueSearch", "Stack"});
      assertTrue(first + " > " + second + " does not hold.", first > second);
   }
}
