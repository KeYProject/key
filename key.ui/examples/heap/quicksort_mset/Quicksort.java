/**
 * This shows how MultiSets can be used to verify the permutation property
 * of a sorting algorithm.
 * FIXME: The sortedness property is NOT shown.
 * The source code is the same as quicksort/QuickSort.java but the present
 * specification is proven automatically, without proof scripts.
 *
 * @author Silvia Zoraqi, Lukas Grätz, 2025
 *
 * based on:
 * @author Mattias Ulbrich, 2015
 */

class Quicksort {

    /*@ public normal_behaviour
      @  ensures (\mset int k; 0 <= k < array.length; array[k]) == \old((\mset int k; 0 <= k < array.length; array[k]));
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
      @  ensures (\mset int k; 0 <= k < array.length; array[k]) == \old((\mset int k; 0 <= k < array.length; array[k]));
      @  assignable array[*];
      @  measured_by to - from + 1;
      @*/
    private void sort(int[] array, int from, int to) {
        if(from < to) {
            int splitPoint = split(array, from, to);
            sort(array, from, splitPoint-1);
            sort(array, splitPoint+1, to);
        }
    }

    /*@ public normal_behaviour
      @  requires 0 <= from && from < to && to <= array.length-1;
      @  ensures (\mset int k; 0 <= k < array.length; array[k]) == \old((\mset int k; 0 <= k < array.length; array[k]));
      @  ensures from <= \result && \result <= to;
      @  assignable array[*];
      @*/
    private int split(int[] array, int from, int to) {

        int i = from;
        int pivot = array[to];

        /*@
          @ loop_invariant from <= i && i <= j;
          @ loop_invariant from <= j && j <= to;
          @ loop_invariant (\mset int k; 0 <= k < array.length; array[k]) == \old((\mset int k; 0 <= k < array.length; array[k]));
          @ decreases to + to - j - i + 2;
          @ assignable array[*];
          @*/
        for(int j = from; j < to; j++) {
            if(array[j] <= pivot) {
                int t = array[i];
                array[i] = array[j];
                array[j] = t;
                i++;
            }
        }

        // FIXME: this assignment has no effect, it should be a loop invariant
        pivot = array[to];

        array[to] = array[i];
        array[i] = pivot;

        return i;

    }
}
