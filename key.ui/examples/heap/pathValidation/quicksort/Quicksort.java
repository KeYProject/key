/**
 * This example formalizes and verifies the wellknown quicksort
 * algorithm for int-arrays algorithm.  It shows that the array
 * is sorted in  the end and that it contains  a permutation of
 * the original input.
 *
 * The   proofs   for   the  main   method   sort(int[])   runs
 * automatically   while   the   other  two   methods   require
 * interaction.  You   can  load   the  files   "sort.key"  and
 * "split.key"  from the  example's  directory  to execute  the
 * according proof scripts.
 *
 * The permutation property requires some interaction: The idea
 * is that the only actual modification on the array are swaps
 * within the "split" method. The sort method body contains
 * three method invocations which each maintain the permutation
 * property. By a repeated appeal to the transitivity of the
 * permutation property, the entire algorithm can be proved to
 * only permute the array.
 *
 * To establish  monotonicity, the key  is to specify  that the
 * currently  handled block  contains  only  numbers which  are
 * between   the    two   pivot   values    array[from-1]   and
 * array[to]. The first  and last block are exempt  from one of
 * these  conditions  since  they have  only  one  neighbouring
 * block.
 *
 * The  example has  been  added  to show  the  power of  proof
 * scripts.
 *
 * @author Mattias Ulbrich, 2015
 *
 * Modified  to run fully automatically for Retrospective  Path
 * Validation. This is a form of partial verification. We first
 * record a control flow trace (instrumentation for a automatic
 * recording can be done with the help of JavaParser)  and then
 * we validate the the single recorded control flow against the
 * specification (the method contract). No auxialliary specifi-
 * cation needed (no loop invariants, no contracts  for  called
 * methods, no proof scripts)!
 *
 * KeY Strategy Settings:
 *   Loop Treatment: Expand (Transformation)
 *   Method Treatment: Expand
 *
 * Or just load quicksort.key
 *
 * Lukas Gra"tz, 2023/24
 */

package quicksort;

class Quicksort {

    /*@ public normal_behaviour
      @
      @ //-- Below is the recorded control flow trace
      @ //-- (rules for predicates trace_O() & I(), traceIndex() are included in this KeY-version)
      @ requires \dl_traceIndex(0);
      @ requires \dl_trace_I(0);
      @ requires \dl_trace_I(1);
      @ requires \dl_trace_I(2);
      @ requires \dl_trace_O(3);
      @ requires \dl_trace_I(4);
      @ requires \dl_trace_O(5);
      @ requires \dl_trace_I(6);
      @ requires \dl_trace_O(7);
      @ requires \dl_trace_I(8);
      @ requires \dl_trace_O(9);
      @ requires \dl_trace_O(10);
      @ requires \dl_trace_O(11);
      @ requires \dl_trace_I(12);
      @ requires \dl_trace_I(13);
      @ requires \dl_trace_O(14);
      @ requires \dl_trace_I(15);
      @ requires \dl_trace_I(16);
      @ requires \dl_trace_I(17);
      @ requires \dl_trace_O(18);
      @ requires \dl_trace_O(19);
      @ requires \dl_trace_O(20);
      @ requires \dl_trace_I(21);
      @ requires \dl_trace_I(22);
      @ requires \dl_trace_O(23);
      @ requires \dl_trace_O(24);
      @ requires \dl_trace_O(25);
      @ requires \dl_trace_O(26);
      @
      @  //-- the following ensures with seqPerm cannot be shown in auto mode with default options:
      @  //ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @  //-- equivalent ensures with \num_of:
      @  ensures (\forall int j; 0<=j && j < array.length;
      @               (\num_of int i; 0<=i && i < array.length; \old(array[i]) == array[j])
      @            == (\num_of int i; 0<=i && i < array.length;      array[i]  == array[j])
      @          );
      @
      @  ensures (\forall int i; 0<=i && i<array.length-1; array[i] <= array[i+1]);
      @
      @  assignable array[*];
      @*/
    public static void sort(int[] array) {
        if(array.length > 0) { // 0
            sort(array, 0, array.length-1);
        }
    }

    private static void sort(int[] array, int from, int to) {
        if(from < to) { // 1, 12, 21
            int splitPoint = split(array, from, to);
            sort(array, from, splitPoint-1);
            sort(array, splitPoint+1, to);
        } // 11, 20, 25, 26
    }

    private static int split(int[] array, int from, int to) {

        int i = from;
        int pivot = array[to];

        for(int j = from; j < to; j++) { // 2, 4, 6, 8, 13, 15, 17, 22
            if(array[j] <= pivot) { // 16
                int t = array[i];
                array[i] = array[j];
                array[j] = t;
                i++;
            } // 3, 5, 7, 9, 14, 18, 23
        } // 10, 19, 24

        array[to] = array[i];
        array[i] = pivot;

        return i;

    }
}
