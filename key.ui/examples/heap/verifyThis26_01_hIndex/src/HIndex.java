/**
 * This is a KeY solution to challenge 1 of VerifyThis 2026.
 *   originally proposed by Jean-Christophe Filliâtre∗ and Mário Pereira
 *
 * Ada is a young researcher who is actively keeping track of her
 * citation counts. She keeps them is an array, which is sorted in
 * reverse order. These days, it looks as follows:
 * 
 *     12 5 3 3 3 3 2 1 0 0
 * 
 * In other words, her most cited paper is cited 12 times, the second
 * most cited paper is cited 5 times, and so on, for a total of 10
 * papers. Ada notices that she has three papers that are cited at least
 * three times each, but that she is not yet famous enough to have four
 * papers cited at least four times each. She defines her score as the
 * greatest number h such that at least h elements in the array are
 * greater or equal to h. Ada just invented the h-index — but luckily for
 * her, her administration has not yet come with the same idea.  Ada is a
 * good programmer, so she quickly writes a C function to compute the h-
 * index (function compute in Fig. 1). A moment later, she realizes that
 * one of the most fundamental algorithm can be used to compute it more
 * efficiently, and she writes a second C function to compute the h-index
 * (function compute opt in Fig. 1).  Whenever Ada discovers a new
 * citation to one of her papers, she updates her array.  She locates the
 * position in the array corresponding to the paper, increments the value
 * at that position, and then moves it to the left until the array is
 * sorted again. For instance, if her paper at position 5 (counting from
 * 0) gets a new citation, the array ends up in the following state:
 * 
 *     12 5 4 3 3 3 2 1 0 0
 * 
 * The h-index is still 3, though. If later, the paper at position 4 gets
 * a new citation, then the array is updated as follows
 * 
 *     12 5 4 4 3 3 2 1 0 0
 * 
 * and this times the h-index becomes 4.
 * 
 * Ada figures out that updating both the array and the h-index value can
 * be conve- niently done at the same time. This is function update in
 * Fig. 1, where parameter h is the current h-index value and i is the
 * index of the count to be incremented. The function updates the array
 * and returns the new h-index value.
 *
 * Originally proposed by Jean-Christophe Filliâtre∗ and Mário Pereira,
 * curated by Thibault Dardinier and Sacha-Elie Ayoun,
 * KeY solution by Mattias Ulbrich (mainly to showcase JML proof scripts).
 */ 
class HIndex {
   
    /*@ public normal_behaviour
      @  requires (\forall int i,j; 0 <= i < j < a.length; a[i] >= a[j]);
      @  ensures (\forall int x; 0 <= x < \result; a[x] > x);
      @  ensures (\num_of int i; 0 <= i < a.length; a[i] >= \result) >= \result;
      @  ensures (\num_of int i; 0 <= i < a.length; a[i] >= \result + 1) < \result + 1;
      @  ensures 0 <= \result <= a.length;
      @  ensures \result == a.length || a[\result] <= \result;
      @  ensures \result == 0 || a[\result-1] >= \result;
      @  assignable \strictly_nothing;
      @*/
    static int compute(int a[]) {
        int h = 0;
        /*@ loop_invariant 0 <= h <= a.length;
          @ loop_invariant h == 0 || a[h-1] >= h;
          @ loop_invariant (\forall int x; 0 <= x < h; a[x] >= h);
          @ loop_invariant (\num_of int i; 0 <= i < h; a[i] >= h) == h;
          @ assignable \strictly_nothing;
          @ decreases a.length - h + 1;
          @*/
        while (h < a.length && h < a[h])
            h++;

        //@ assert h == a.length || a[h] <= h ;

        /*@ assert (\num_of int i; 0 <= i < h; a[i] >= h + 1) <= h \by {
          @   oss;
          @   rule "bsum_num_of_bounds" occ: 1;
          @   auto;
          @ };
          @*/
        
        /*@ assert (\num_of int i; 0 <= i < a.length; a[i] >= h) ==
          @  (\num_of int i; 0 <= i < h; a[i] >= h) +
          @  (\num_of int i; h <= i < a.length; a[i] >= h);
          @*/

        /*@ assert (\num_of int i; 0 <= i < a.length; a[i] >= h + 1) ==
          @  (\num_of int i; 0 <= i < h; a[i] >= h + 1) +
          @  (\num_of int i; h <= i < a.length; a[i] >= h + 1);
          @*/
        
        /*@ assert (\num_of int i; 0 <= i < a.length; a[i] >= h) >= h \by {
          @  oss;
          @  rule "bsum_positive1" occ: 0 on: (\num_of int i; h <= i < a.length; a[i] >= h);
          @  auto;
          @ };
          @*/

        //@ assert (\num_of int i; h <= i < a.length; a[i] >= h + 1) == 0;
        
        return h;
    }

    // the same, more efficiently
    /*@ public normal_behaviour
      @  requires (\forall int i,j; 0 <= i < j < a.length; a[i] >= a[j]);
      @  ensures (\forall int x; 0 <= x < \result; a[x] > x);
      @  ensures (\num_of int i; 0 <= i < a.length; a[i] >= \result) >= \result;
      @  ensures (\num_of int i; 0 <= i < a.length; a[i] >= \result + 1) < \result + 1;
      @  ensures \result == a.length || a[\result] <= \result;
      @  ensures \result == 0 || a[\result-1] >= \result;
      @  assignable \strictly_nothing;
      @*/
    static int compute_opt(int a[]) {
        int lo = 0, hi = a.length;

        /*@ loop_invariant 0 <= lo <= hi <= a.length;
          @ loop_invariant lo == 0 || a[lo-1] >= lo;
          @ loop_invariant (\forall int x; 0 <= x < lo; a[x] >= lo);
          @ loop_invariant (\forall int x; hi <= x < a.length; a[x] <= hi);
          @ assignable \strictly_nothing;
          @ decreases hi - lo + 1;
          @*/
        while (lo < hi) {
            int mid = lo + (hi - lo) / 2;
            if (a[mid] <= mid) hi = mid;
            else lo = mid + 1;
        }

        lemma1(lo, a);
        
        //@ assert (\num_of int i; 0 <= i < lo; a[i] >= lo) == lo;
        
        /*@ assert (\num_of int i; 0 <= i < lo; a[i] >= lo + 1) <= lo \by {
          @   oss;
          @   rule "bsum_num_of_bounds" occ: 1;
          @   auto;
          @ };
          @*/
        
        /*@ assert (\num_of int i; 0 <= i < a.length; a[i] >= lo) ==
          @  (\num_of int i; 0 <= i < lo; a[i] >= lo) +
          @  (\num_of int i; lo <= i < a.length; a[i] >= lo);
          @*/

        /*@ assert (\num_of int i; 0 <= i < a.length; a[i] >= lo + 1) ==
          @  (\num_of int i; 0 <= i < lo; a[i] >= lo + 1) +
          @  (\num_of int i; lo <= i < a.length; a[i] >= lo + 1);
          @*/
        
        /*@ assert (\num_of int i; 0 <= i < a.length; a[i] >= lo) >= lo  \by {
          @  oss;
          @  rule "bsum_positive1" occ: 0 on: (\num_of int i; lo <= i < a.length; a[i] >= lo);
          @  auto;
          @ };
          @*/

        //@ assert (\num_of int i; lo <= i < a.length; a[i] >= lo + 1) == 0;
        
        return lo;
    }

    /*@ public normal_behaviour
      @  requires (\forall int i; 0 <= i < lo; a[i] >= lo);
      @  requires 0 <= lo <= a.length;
      @  ensures (\num_of int i; 0 <= i < lo; a[i] >= lo) == lo;
      @  assignable \strictly_nothing;
      @*/
    static void lemma1(int lo, int[] a) {
        /*@ loop_invariant (\num_of int i; 0 <= i < r; a[i] >= lo) == r;
          @ loop_invariant 0 <= r <= lo;
          @ decreases lo - r;
          @ assignable \strictly_nothing;
          @*/
        for(int r = 0; r < lo; r++) {}
    }

    /*@ normal_behaviour
      @  requires 0 <= i < a.length;
      @  requires 0 <= h <= a.length;
      @  requires (\forall int i,j; 0 <= i < j < a.length; a[i] >= a[j]);
      @  requires h == 0 || a[h-1] >= h;
      @  requires h == a.length || a[h] <= h;
      @  ensures \result == 0 || a[\result-1] >= \result;
      @  ensures \result == a.length || a[\result] <= \result;
      @  ensures 0 <= \result <= a.length;
      @  ensures (\exists int p; 0 <= p < a.length; \old(a[p] == a[i]) &&
      @      a[p] == \old(a[p] + 1) &&
      @      (\forall int q; 0 <= q < a.length && q != p; a[q] == \old(a[q])));
      @  ensures (\forall int i,j; 0 <= i < j < a.length; a[i] >= a[j]);
      @  assignable a[*];
      @*/
    static int update(int a[], int h, int i) {
        int x = a[i];
        int lo = 0, hi = i;
        /*@ loop_invariant 0 <= lo <= hi < a.length;
          @ loop_invariant (\forall int f; 0 <= f < lo; a[f] > x);
          @ loop_invariant (\forall int g; hi <= g <= i; a[g] == x);
          @ loop_invariant a[i] == a[hi];
          @ loop_invariant lo > 0 ==> a[lo-1] > a[i];
          @ assignable \strictly_nothing;
          @ decreases hi - lo + 1;
          @*/
        while (lo < hi) {
            //@ ghost int diff = hi - lo;

            int mid;
            //@ ensures \dl_mod(diff,2) == 0 ==> 2*mid == 2*lo + diff;
            //@ ensures \dl_mod(diff,2) == 1 ==> 2*mid == 2*lo + diff - 1;
            //@ signals (Throwable e) false;
            //@ assignable \strictly_nothing;
            { mid = lo + (hi-lo) / 2; }

            if (a[mid] == x) hi = mid;
            else lo = mid + 1;
        }

        a[lo]++;

        if (lo == h && a[lo] == h+1) {
            return h+1;
        } else {
            return h;
        }
    }
}
