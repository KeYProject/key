
import java.util.Arrays;

public class ArrayList implements List {

    private /*@ nullable @*/ /*@ spec_public */ int[] array;
    private int size = 0;
    
    /*@ private invariant array != null;
      @ private invariant footprint == \set_union(array[*], this.*);
      @ private invariant 0 <= size && size <= array.length;
      @ private invariant (\forall int i; 0 <= i && i < size; array[i] != null);
      @
      @ private invariant seq.length == size;
      @ private invariant (\forall int i; 0 <= i && i < size; array[i] == (\bigint)seq[i]);
      @*/

    /*@ public normal_behaviour
      @   ensures seq == \seq_empty && \fresh(footprint);
      @*/
    public /*@ pure @*/ ArrayList() {
        this.array = new int[10];
        //@ set seq = \seq_empty;
        //@ set footprint = \set_union(\all_fields(array), \all_fields(this));
    }

    public int get(int index) {
        return array[index];
    }

    public int size() {
        return size;
    }

    public void add(int o) {
        if(size == array.length) {
            array = Arrays.copyOf(array, array.length + 10);
        }
        array[size++] = o;
        //@ set seq = \seq_concat(seq, \seq_singleton(o));
        //@ set footprint = \set_union(\all_fields(array), \all_fields(this));
    }

    public int find(int value) {
        return binSearch(value);
    }

    /*@ private normal_behaviour
      @   requires (\forall int x; (\forall int y; 0<=x<y<size; array[x] <= array[y]));  
      @   ensures -1 <= \result < size;
      @   ensures (\exists int idx; 0<=idx<size; array[idx] == v) ?
      @      \result >= 0 && array[\result] == v : \result == -1;
      @   assignable \nothing;
      @*/
    private int binSearch(int v) {
        int l = 0;
        int r = size - 1;

        if(size == 0) return -1;
        if(size == 1) return array[0] == v ? 0 : -1;

        /*@ loop_invariant 0 <= l && l < r && r < size
          @    && (\forall int x; 0 <= x && x < l; array[x] < v)
          @    && (\forall int x; r < x && x < size; v < array[x]);
          @ assignable \nothing;
          @ decreases r - l;
          @*/
        while(r > l + 1) {
            int mid = l + (r - l) / 2;
            if(array[mid] == v) {
                return mid;
            } else if(array[mid] > v) {
                r = mid;
            } else {
                l = mid;
            }
        }

        if(array[l] == v) return l;
        if(array[r] == v) return r;
        return -1;
    }

    /*@ public normal_behaviour
      @  ensures \dl_seqPerm(\old(seq), seq);
      @  ensures  (\forall int x; (\forall int y; 0<=x<y<seq.length; (\bigint)seq[x] <= (\bigint)seq[y]));
      @  assignable footprint;
      @*/
    public void sort() {

        /*@ loop_invariant 0 <= i <= size-1;
          @ loop_invariant (\forall int k; 0<=k<i; array[k] <= array[k+1]);
          @ loop_invariant (\forall int l; i<=l<size; array[i] <= array[l]);
          @ loop_invariant \dl_seqPerm(\old(seq), seq);
          @ loop_invariant \invariant_for(this);
          @ assignable array[*];
          @ decreases size - i;
          @*/
        for(int i = 0; i < size-1; i++) {
            int min = i+1;
            /*@ loop_invariant i+2 <= j <= size;
              @ loop_invariant i+2 <= min < j;
              @ loop_invariant (\forall int x; i+1<=x<j; array[x] <= array[min]);
              @ assignable \strictly_nothing;
              @ decreases size - i;
              @*/
            for(int j = i+2; j < size; j++) {
                if(array[j] < array[min]) {
                    min = j;
                }
            }
            swap(i, min);
        }
    }

    /*@ private normal_behaviour
      @  requires 0 <= a < size;
      @  requires 0 <= b < size;
      @  ensures array[a] == \old(array[b]);
      @  ensures array[b] == \old(array[a]);
      @  ensures \dl_seqPerm(\old(seq), seq);
      @  assignable array[a], array[b], seq;
      @*/
    private void swap(int a, int b) {
        int t = array[a];
        array[a] = array[b];
        array[b] = t;
        //@ set seq = \seq_put(seq, a, array[a]);
        //@ set seq = \seq_put(seq, b, array[b]);
    }
}
