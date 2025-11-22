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
 * Translated to the use of JML proof scripts in 2025. Currently,
 * this still increases the size of proof.
 *
 * @author Mattias Ulbrich, 2015, 2025
 */

class Quicksort {

    /*@ public normal_behaviour
      @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @  ensures (\forall int i; 0<=i && i<array.length-1; array[i] <= array[i+1]);
      @  assignable array[*];
      @*/
    public void sort(int[] array) {
        if(array.length > 0) {
            sort(array, 0, array.length-1);
        }
    }

    /*@ public normal_behaviour
      @  requires 0 <= from;
      @  requires to < array.length;
      @  requires from > 0 ==> (\forall int x; from<=x && x<=to; array[x] > array[from-1]);
      @  requires to < array.length-1 ==> (\forall int x; from<=x && x<=to; array[x] <= array[to+1]);
      @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @  ensures (\forall int i; from<=i && i<to; array[i] <= array[i+1]);
      @  ensures from > 0 ==> (\forall int x; from<=x && x<=to; array[x] > array[from-1]);
      @  ensures to < array.length-1 ==> (\forall int x; from<=x && x<=to; array[x] <= array[to+1]);
      @  assignable array[from..to];
      @  measured_by to - from + 1;
      @*/
    private void sort(int[] array, int from, int to) {
        if(from < to) {
            //@ ghost \seq seq0 = \dl_array2seq(array);
            int splitPoint = split(array, from, to);
            //@ ghost \seq seq1 = \dl_array2seq(array);
            sort(array, from, splitPoint-1);
            //@ ghost \seq seq2 = \dl_array2seq(array);
            sort(array, splitPoint+1, to);
            //@ ghost \seq seq3 = \dl_array2seq(array);
            /*@ assert \dl_seqPerm(seq3, seq0) \by {
              @   assert \dl_seqPerm(seq1, seq0) \by auto;
              @   assert \dl_seqPerm(seq2, seq0) \by auto;
              @   auto;
              @ } */
        }
    }

    /*@ public normal_behaviour
      @  requires 0 <= from && from < to && to <= array.length-1;
      @  requires from > 0 ==> (\forall int x; from<=x && x<=to; array[from-1] < array[x]);
      @  requires to < array.length-1 ==> (\forall int y; from<=y && y<=to; array[y] <= array[to+1]);
      @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @  ensures from <= \result && \result <= to;
      @  ensures (\forall int m; from <= m && m <= \result; array[m] <= array[\result]);
      @  ensures (\forall int n; \result < n && n <= to; array[n] > array[\result]);
      @  ensures from > 0 ==> (\forall int x; from<=x && x<=to; array[from-1] < array[x]);
      @  ensures to < array.length-1 ==> (\forall int y; from<=y && y<=to; array[y] <= array[to+1]);
      @  assignable array[from..to];
      @*/
    private int split(int[] array, int from, int to) {

        int i = from;
        int pivot = array[to];

        /*@
          @ loop_invariant from <= i && i <= j;
          @ loop_invariant from <= j && j <= to;
          @ loop_invariant \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
          @ loop_invariant (\forall int k; from <= k && k < i; array[k] <= pivot);
          @ loop_invariant (\forall int l; i <= l && l < j; array[l] > pivot);
          @ loop_invariant from > 0 ==> (\forall int x; from<=x && x<=to; array[from-1] < array[x]);
          @ loop_invariant to < array.length-1 ==> (\forall int y; from<=y && y<=to; array[y] <= array[to+1]);
          @ decreases to + to - j - i + 2;
          @ assignable array[from..to-1];
          @*/
        for(int j = from; j < to; j++) {
            if(array[j] <= pivot) {
                int t = array[i];
                array[i] = array[j];
                array[j] = t;
                /*@ assert \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array))) \by {
                  @  oss;
                  @  rule "seqPermFromSwap";
                  @  rule "andRight" \by {
                  @    case "Case 1": // the first of the two conjuncts is easy
                  @      auto;
                  @    case "Case 2": // the 2nd requires instantiations:
                  @      instantiate hide:true var:"iv" with:i;
                  @      instantiate hide:true var:"jv" with:j;
                  @      auto;
                  @  }
                  @ };  */
                i++;
            }
        }

        array[to] = array[i];
        array[i] = pivot;

         /*@ assert \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array))) \by {
           @  oss;
           @  rule "seqPermFromSwap";
           @  rule "andRight" \by {
           @    case "Case 1": // the first of the two conjuncts is easy
           @      auto;
           @    case "Case 2": // the 2nd requires instantiations:
           @      instantiate hide:true var:"iv" with:i;
           @      instantiate hide:true var:"jv" with:to;
           @      auto;
           @  }
           @ };  */

        return i;

    }
}
