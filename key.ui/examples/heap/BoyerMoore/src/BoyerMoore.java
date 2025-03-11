
/**
 * This is a KeY verification example for the Boyer Moore 
 *  majority vote algorithm.
 *
 * The challenge is as followed:
 *   Compute in linear time the majority 
 *   of an array of integers if it
 *   exists, report its absence otherwise, .
 * An element m is the majority element if more than half of the 
 * entries in the array hold m.
 *
 * Suggested by J.C. Filliâtre as an example during VerifyThis 24.
 *
 * @see https://en.wikipedia.org/wiki/Boyer-Moore_majority_vote_algorithm
 * @author Mattias Ulbrich
 */
class BoyerMoore {

    /*@ private normal_behaviour
      @  requires 0 <= k <= a.length;
      @  ensures \result == (\num_of int l; 0<=l<k; a[l] == v);
      @  measured_by k;
      @  accessible a[*];
      @ model int count(int[] a, \bigint k, \bigint v) {
      @   return k == 0 ? 0 :
      @     ((a[k-1] == v ? 1 : 0) + count(a, k-1, v));
      @ }
      @*/

    /*@ public normal_behaviour
      @  requires \static_invariant_for(IntOpt);
      @  ensures  \result.present ==> count(a, a.length, \result.value) > a.length/2;
      @
      @  ensures !\result.present ==> !(\exists int m; count(a, a.length, m) > a.length/2);
      @
      @  assignable \nothing;
      @*/
    public IntOpt bm(int[] a) {

        int mc = 0;
        int mx = 0;
        
        /*@ loop_invariant 0 <= k <= a.length;
          @ loop_invariant mc >= 0;
          @ loop_invariant 2 * count(a, k, mx) <= k + mc;
          @ loop_invariant (\forall int x; x != mx; 2 * count(a, k, x) <= k - mc);
          @ assignable \strictly_nothing;
          @ decreases a.length - k;
          @*/
        for(int k=0; k < a.length; k++) {
            if(mc == 0) {
                mc = 1;
                mx = a[k];
            } else if(mx == a[k]) {
                mc++;
            } else {
                mc--;
            }
        }

        if(mc == 0) return IntOpt.NONE;

        int cnt = 0;
        /*@ loop_invariant 0 <= r <= a.length;
          @ loop_invariant cnt == count(a, r, mx);
          @ loop_invariant cnt <= a.length / 2;
          @ assignable \strictly_nothing;
          @ decreases a.length - r;
          @*/
        for(int r=0; r < a.length; r++) {
            if(mx == a[r]) {
                if(++cnt > a.length / 2) {
                    // This should be a ghost call which
                    // is currently unsupported.
                    monoLemma(a, r + 1, mx);
                    return new IntOpt(mx);
                }
            }
        }
        
        return IntOpt.NONE;
    }

    // This should be ghost which is currently unsupported.
    /*@ private normal_behaviour
      @  requires 0 <= k <= a.length;
      @  ensures count(a, k, v) <= count(a, a.length, v);
      @  assignable \strictly_nothing; 
      @  measured_by a.length - k;
      @*/
    private void monoLemma(int[] a, int k, int v) {
        if(k == a.length) return;
        monoLemma(a, k+1, v); 
    }
    
}

/**
 * This class is used to represent an optional integer value.
 * The field  present indicates the presence of a result,
 * value contains that value.
 */
final class IntOpt {
    public static final IntOpt NONE;
    static {
        NONE = new IntOpt(0);
        NONE.present = false;
    }
    
    //@ public static invariant !NONE.present;

    /*@ spec_public */ private boolean present;
    /*@ spec_public */ private int value;

    // No contract for this construtor, the code will be inlined.
    IntOpt(int value) {
        this.present = true;
        this.value = value;
    }
}
