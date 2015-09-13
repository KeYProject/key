class Quicksort {


    /*@ public normal_behaviour
      @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @  ensures (\forall int i; 0<=i && i<array.length; a[i] <= a[i+1]);
      @  assignable array[*];
      @*/
    public void sort(int[] array) {
        sort(array, 0, array.length-1);
    }

    /*@ public normal_behaviour
      @  requires 0<=from && from < array.length;
      @  requires 0<=to && to < array.length;
      @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @  ensures (\forall int i; from<=i && i<to; a[i] <= a[i+1]);
      @  assignable array[from..to];
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
      @  ensures \dl_seqPerm(\dl_array2seq(array), \old(\dl_array2seq(array)));
      @  ensures from <= \result && \result <= to;
      @  ensures (\forall int m; from <= m && m <= \result; array[m] <= array[\result]);
      @  ensures (\forall int n; \result < n && n <= to; array[n] > array[\result]);
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
          @ decreases to + to - j - i + 2;
          @ assignable array[from..to-1];
          @*/
        for(int j = from; j < to; j++) {
            if(array[j] <= pivot) {
                int t = array[i];
                array[i] = array[j];
                array[j] = t;
                i++;
            }
        }

        array[to] = array[i];
        array[i] = pivot;

        return i;

    }
}
