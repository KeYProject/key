package java.util;
/*
 * Copyright 2009 Google Inc.  All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */



/**
 * A stable, adaptive, iterative mergesort that requires far fewer than
 * n lg(n) comparisons when running on partially sorted arrays, while
 * offering performance comparable to a traditional mergesort when run
 * on random arrays.  Like all proper mergesorts, this sort is stable and
 * runs O(n log n) time (worst case).  In the worst case, this sort requires
 * temporary storage space for n/2 object references; in the best case,
 * it requires only a small constant amount of space.
 *
 * This implementation was adapted from Tim Peters's list sort for
 * Python, which is described in detail here:
 *
 *   http://svn.python.org/projects/python/trunk/Objects/listsort.txt
 *
 * Tim's C code may be found here:
 *
 *   http://svn.python.org/projects/python/trunk/Objects/listobject.c
 *
 * The underlying techniques are described in this paper (and may have
 * even earlier origins):
 *
 *  "Optimistic Sorting and Information Theoretic Complexity"
 *  Peter McIlroy
 *  SODA (Fourth Annual ACM-SIAM Symposium on Discrete Algorithms),
 *  pp 467-474, Austin, Texas, 25-27 January 1993.
 *
 * While the API to this class consists solely of static methods, it is
 * (privately) instantiable; a TimSort instance holds the state of an ongoing
 * sort, assuming the input array is large enough to warrant the full-blown
 * TimSort. Small arrays are sorted in place, using a binary insertion sort.
 *
 * @author Josh Bloch
 */
public class TimSort/**/ {
	
    /*@ private invariant
      @    runBase.length == runLen.length && runBase != runLen
      @ && a != runBase && a != runLen && a != tmp && a != null
      @ && tmp != runLen && tmp != runBase && tmp != null
      @ && (a.length < 120                        ==> runLen.length ==  4)
      @ && (a.length >= 120 && a.length < 1542    ==> runLen.length ==  9)
      @ && (a.length >= 1542 && a.length < 119151 ==> runLen.length == 18)
      @ && (a.length >= 119151                    ==> runLen.length == 39)
      @ && (runBase[0] + (\sum int i; 0<=i && i<stackSize; (\bigint)runLen[i])
      @     <= a.length)
      @ && (0 <= stackSize && stackSize <= runLen.length)
      @ && (\forall \bigint i; 0<=i && i<(\bigint)stackSize-4;
      @        \dl_elemInv(runLen, i, MIN_MERGE/2))
      @ && \dl_elemBiggerThanNext(runLen, (\bigint)stackSize-4)
      @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-3, MIN_MERGE/2)
      @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-2, MIN_MERGE/2)
      @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-1, 1)
      @ && (\dl_elemLargerThanBound(runBase, 0, 0))
      @ && (\forall \bigint i; 0<=i && i<(\bigint)stackSize-1;
      @        (\bigint)runBase[i] + runLen[i] == runBase[(\bigint)i+1]);
      @*/
	
    /*@ private accessible \inv: minGallop, runBase, runLen, a, c, tmp, runBase[*], runLen[*], stackSize;
      @*/
    
    /**
     * This is the minimum sized sequence that will be merged.  Shorter
     * sequences will be lengthened by calling binarySort.  If the entire
     * array is less than this length, no merges will be performed.
     *
     * This constant should be a power of two.  It was 64 in Tim Peter's C
     * implementation, but 32 was empirically determined to work better in
     * this implementation.  In the unlikely event that you set this constant
     * to be a number that's not a power of two, you'll need to change the
     * {@link #minRunLength} computation.
     *
     * If you decrease this constant, you must change the stackLen
     * computation in the TimSort constructor, or you risk an
     * ArrayOutOfBounds exception.  See listsort.txt for a discussion
     * of the minimum stack length required as a function of the length
     * of the array being sorted and the minimum merge sequence length.
     */
    private static final int MIN_MERGE = 32;

    /**
     * The array being sorted.
     */
    private /*@ nullable @*/ final Object[] a;

    /**
     * The comparator for this sort.
     */
    private final Comparator/*<? super T>*/ c;

    /**
     * When we get into galloping mode, we stay there until both runs win less
     * often than MIN_GALLOP consecutive times.
     */
    private static final int  MIN_GALLOP = 7;

    /**
     * This controls when we get *into* galloping mode.  It is initialized
     * to MIN_GALLOP.  The mergeLo and mergeHi methods nudge it higher for
     * random data, and lower for highly structured data.
     */
    private int minGallop = MIN_GALLOP;

    /**
     * Maximum initial size of tmp array, which is used for merging.  The array
     * can grow to accommodate demand.
     *
     * Unlike Tim's original C version, we do not allocate this much storage
     * when sorting smaller arrays.  This change was required for performance.
     */
    private static final int INITIAL_TMP_STORAGE_LENGTH = 256;

    /**
     * Temp storage for merges.
     */
    private /*@ nullable @*/ Object[] tmp; // Actual runtime type will be Object[], regardless of T

    // \dl_inInt ensures that minGallop is in integer range; Integer.MIN_VALUE <= minGallop <= Integer.MAX_VALUE
    //@ private invariant \typeof(tmp) == \type(Object[]) && \dl_inInt(minGallop);
    
    /**
     * A stack of pending runs yet to be merged.  Run i starts at
     * address base[i] and extends for len[i] elements.  It's always
     * true (so long as the indices are in bounds) that:
     *
     *     runBase[i] + runLen[i] == runBase[i + 1]
     *
     * so we could cut the storage for this, but it's a minor amount,
     * and keeping all the info explicit simplifies the code.
     */
    private int stackSize = 0;  // Number of pending runs on stack
    private final int[] runBase;
    private final int[] runLen;

    /**
     * Creates a TimSort instance to maintain the state of an ongoing sort.
     *
     * @param a the array to be sorted
     * @param c the comparator to determine the order of the sort
     */

    /*@ private normal_behavior
      @   requires
      @     a != null;
      @   ensures
      @     a == this.a && c == this.c && stackSize == 0 && runBase[0] == 0;
      @*/
    private TimSort(/*@ nullable @*/ Object[] a, Comparator/*<? super T>*/ c) {
        this.a = a;
        this.c = c;

        // Allocate temp storage (which may be increased later if necessary)
        int len = a.length;
        Object[] newArray = (Object[]) new Object[len < 2 * INITIAL_TMP_STORAGE_LENGTH ?
                                        len >>> 1 : INITIAL_TMP_STORAGE_LENGTH];
        tmp = newArray;

        /*
         * Allocate runs-to-be-merged stack (which cannot be expanded).  The
         * stack length requirements are described in listsort.txt.  The C
         * version always uses the same stack length (85), but this was
         * measured to be too expensive when sorting "mid-sized" arrays (e.g.,
         * 100 elements) in Java.  Therefore, we use smaller (but sufficiently
         * large) stack lengths for smaller arrays.  The "magic numbers" in the
         * computation below must be changed if MIN_MERGE is decreased.  See
         * the MIN_MERGE declaration above for more information.
         */
        int stackLen = (len <    120  ?  4 :
                        len <   1542  ?  9 :
                        len < 119151  ? 18 : 39);
        runBase = new int[stackLen];
        runLen = new int[stackLen];
    }

    /*
     * The next two methods (which are package private and static) constitute
     * the entire API of this class.  Each of these methods obeys the contract
     * of the public method with the same signature in java.util.Arrays.
     */

    /*@ normal_behavior
      @   requires
      @     a != null;
      @   ensures
      @     true;
      @*/
    static void sort(/*@ nullable @*/ Object[] a, Comparator/*<? super T>*/ c) {
        sort(a, 0, a.length, c);
    }

    /*@ normal_behavior
      @   requires
      @     a != null && 0 <= lo && lo <= hi && hi <= a.length;
      @   ensures
      @     true;
      @*/
    static void sort(/*@ nullable @*/ Object[] a, int lo, int hi, Comparator/*<? super T>*/ c) {
        if (c == null) {
            Arrays.sort(a, lo, hi);
            return;
        }

        rangeCheck(a.length, lo, hi);
        int nRemaining  = hi - lo;
        if (nRemaining < 2)
            return;  // Arrays of size 0 and 1 are always sorted

        // If array is small, do a "mini-TimSort" with no merges
        if (nRemaining < MIN_MERGE) {
            int initRunLen = countRunAndMakeAscending(a, lo, hi, c);
            binarySort(a, lo, hi, lo + initRunLen, c);
            return;
        }

        /**
         * March over the array once, left to right, finding natural runs,
         * extending short natural runs to minRun elements, and merging runs
         * to maintain stack invariant.
         */
        TimSort/**/ ts = new TimSort/*<>*/(a, c);
        int minRun = minRunLength(nRemaining);
        /*@ loop_invariant
          @    (0 <= ts.stackSize && ts.stackSize <= ts.runLen.length)
          @ && (ts.tmp != a && ts.tmp != ts.runLen && ts.tmp != ts.runBase && ts.tmp != null)
          @ && (0 <= nRemaining && minRun >= MIN_MERGE/2 && (\bigint)lo + nRemaining == hi)
          @ && (lo == \old(lo) + (\sum int i; 0<=i && i<ts.stackSize; (\bigint)ts.runLen[i]))
          @ && (\forall \bigint i; 0<=i && i<(\bigint)ts.stackSize-2;
          @        \dl_elemInv(ts.runLen, i, MIN_MERGE/2))
          @ && \dl_elemBiggerThanNext(ts.runLen, (\bigint)ts.stackSize-2)
          @ && \dl_elemLargerThanBound(ts.runLen, (\bigint)ts.stackSize-2, MIN_MERGE/2)
          @ && \dl_elemLargerThanBound(ts.runLen, (\bigint)ts.stackSize-1, 1)
          @ && (nRemaining  > 0 ==>
          @        \dl_elemLargerThanBound(ts.runLen, (\bigint)ts.stackSize-1, MIN_MERGE/2))
          @ && (\forall \bigint i; 0<=i && i<(\bigint)ts.stackSize-1;
          @        (\bigint)ts.runBase[i] + ts.runLen[i] == ts.runBase[(\bigint)i+1])
	  @ && (\typeof(ts.tmp) == \type(Object[]) && \dl_inInt(ts.minGallop))
	  @ && (ts.stackSize > 0 ==> ts.runBase[0] == \old(lo))
	  @ && (ts.stackSize == 0 ==> (nRemaining > 0 && ts.runBase[0] == 0));
          @ assignable
          @   ts.stackSize,
          @   ts.tmp,
          @   ts.runBase[0 .. (\bigint)ts.runBase.length-1],
          @   ts.runLen[0 .. (\bigint)ts.runLen.length-1],
          @   \infinite_union(nullable Object[] array; array[0 .. (\bigint)array.length-1]),
          @   ts.minGallop;
          @ decreases nRemaining;
          @*/
        do {
            // Identify next run
            int runLen = countRunAndMakeAscending(a, lo, hi, c);

            // If run is short, extend to min(minRun, nRemaining)
            /*@ normal_behavior
              @ ensures
              @      (\old(runLen <  minRun && nRemaining <= minRun) ==> runLen == nRemaining)
              @   && (\old(runLen <  minRun && nRemaining  > minRun) ==> runLen == minRun)
              @   && (\old(runLen >= minRun)                         ==> runLen == \old(runLen));
              @ assignable
              @   a[0 .. (\bigint)a.length-1];
              @*/
            {
            if (runLen < minRun) {
                int force = nRemaining <= minRun ? nRemaining : minRun;
                binarySort(a, lo, lo + force, lo + runLen, c);
                runLen = force;
            }
            }

            // Push run onto pending-run stack, and maybe merge
            ts.pushRun(lo, runLen);
            ts.newMergeCollapse();

            // Advance to find next run
            lo += runLen;
            nRemaining -= runLen;
        } while (nRemaining != 0);

        // Merge all remaining runs to complete sort
        assert lo == hi;
        ts.mergeForceCollapse();
        assert ts.stackSize == 1;
    }

    /**
     * Sorts the specified portion of the specified array using a binary
     * insertion sort.  This is the best method for sorting small numbers
     * of elements.  It requires O(n log n) compares, but O(n^2) data
     * movement (worst case).
     *
     * If the initial part of the specified range is already sorted,
     * this method can take advantage of it: the method assumes that the
     * elements from index {@code lo}, inclusive, to {@code start},
     * exclusive are already sorted.
     *
     * @param a the array in which a range is to be sorted
     * @param lo the index of the first element in the range to be sorted
     * @param hi the index after the last element in the range to be sorted
     * @param start the index of the first element in the range that is
     *        not already known to be sorted ({@code lo <= start <= hi})
     * @param c comparator to used for the sort
     */

    /*@ private normal_behavior
      @   requires
      @     a != null && 0 <= lo && lo <= start && start <= hi && hi <= a.length && lo < hi;
      @   ensures
      @     true;
      @   assignable
      @     a[0 .. (\bigint)a.length-1];
      @*/
    private static  void binarySort(/*@ nullable @*/ Object[] a, int lo, int hi, int start,
                                       Comparator/*<? super T>*/ c) {
        assert lo <= start && start <= hi;
        /*@ normal_behavior
          @ requires
          @   true;
          @ ensures
          @      (\old(start) == lo ==> start == (\bigint)\old(start)+1)
          @   && (\old(start) != lo ==> start == \old(start));
          @ assignable
          @   \nothing;
          @*/
        {
	    if (start == lo)
            start++;
        }
	/*@ loop_invariant 
	  @     start >= lo && start <= hi;
	  @ decreases hi-start;
	  @ assignable a[0 .. a.length-1];
	  @*/
        for ( ; start < hi; start++) {
            Object pivot = a[start];

            // Set left (and right) to the index where a[start] (pivot) belongs
            int left = lo;
            int right = start;
            assert left <= right;
            /*
             * Invariants:
             *   pivot >= all in [lo, left).
             *   pivot <  all in [right, start).
             */
	    /*@ loop_invariant 
	      @     left >= 0 && left <= right && right <= start && left <= (right+left) >>> 1 && (right+left) >>> 1 <= right && left <= a.length;
	      @ decreases ((\bigint)right - (\bigint)left) + (\bigint)1, right;
	      @ assignable \nothing;
	      @*/
            while (left < right) {
                int mid = (left + right) >>> 1;
                if (c.compare(pivot, a[mid]) < 0)
                    right = mid;
                else
                    left = mid + 1;
            }
            assert left == right;

            /*
             * The invariants still hold: pivot >= all in [lo, left) and
             * pivot < all in [left, start), so pivot belongs at left.  Note
             * that if there are elements equal to pivot, left points to the
             * first slot after them -- that's why this sort is stable.
             * Slide elements over to make room for pivot.
             */
            int n = start - left;  // The number of elements to move
            // Switch is just an optimization for arraycopy in default case
            switch (n) {
                case 2:  a[left + 2] = a[left + 1];
                case 1:  a[left + 1] = a[left];
                         break;
                default: System.arraycopy(a, left, a, left + 1, n);
            }
            a[left] = pivot;
        }
    }

    /**
     * Returns the length of the run beginning at the specified position in
     * the specified array and reverses the run if it is descending (ensuring
     * that the run will always be ascending when the method returns).
     *
     * A run is the longest ascending sequence with:
     *
     *    a[lo] <= a[lo + 1] <= a[lo + 2] <= ...
     *
     * or the longest descending sequence with:
     *
     *    a[lo] >  a[lo + 1] >  a[lo + 2] >  ...
     *
     * For its intended use in a stable mergesort, the strictness of the
     * definition of "descending" is needed so that the call can safely
     * reverse a descending sequence without violating stability.
     *
     * @param a the array in which a run is to be counted and possibly reversed
     * @param lo index of the first element in the run
     * @param hi index after the last element that may be contained in the run.
              It is required that {@code lo < hi}.
     * @param c the comparator to used for the sort
     * @return  the length of the run beginning at the specified position in
     *          the specified array
     */

    /*@ private normal_behavior
      @   requires
      @     a != null && 0 <= lo && lo < hi && hi <= a.length;
      @   ensures
      @     0 <= \result && \result <= (\bigint)hi-lo;
      @   assignable
      @     a[0 .. (\bigint)a.length-1];
      @*/
    private static int countRunAndMakeAscending(/*@ nullable @*/ Object[] a, int lo, int hi,
                                                    Comparator/*<? super T>*/ c) {
        assert lo < hi;
        int runHi = lo + 1;
        if (runHi == hi)
            return 1;

        // Find end of run, and reverse range if descending
        if (c.compare(a[runHi++], a[lo]) < 0) { // Descending
            /*@ loop_invariant
              @    lo < runHi && runHi <= hi;
              @ assignable
              @    \nothing;
              @ decreases
              @    (\bigint)hi - runHi;
              @*/
            while (runHi < hi && c.compare(a[runHi], a[runHi - 1]) < 0)
                runHi++;
            reverseRange(a, lo, runHi);
        } else {                              // Ascending
            /*@ loop_invariant
              @    lo < runHi && runHi <= hi;
              @ assignable
              @    \nothing;
              @ decreases
              @    (\bigint)hi - runHi;
              @*/
            while (runHi < hi && c.compare(a[runHi], a[runHi - 1]) >= 0)
                runHi++;
        }

        return runHi - lo;
    }

    /**
     * Reverse the specified range of the specified array.
     *
     * @param a the array in which a range is to be reversed
     * @param lo the index of the first element in the range to be reversed
     * @param hi the index after the last element in the range to be reversed
     */

    /*@ private normal_behavior
      @ requires
      @   a != null && 0 <= lo && lo <= hi && hi <= a.length;
      @ ensures
      @   true;
      @ assignable
      @   a[0 .. (\bigint)a.length-1];
      @*/
    private static void reverseRange(/*@ nullable @*/ Object[] a, int lo, int hi) {
        hi--;
        /*@ loop_invariant
          @      \old(lo) <= lo && lo <= (\bigint)hi + 1 && hi < \old(hi)
          @   && lo-\old(lo) == (\bigint)\old(hi)-1-hi
          @   && (\forall int i; \old(lo)<=i && i<lo;
          @              a[i] == \old(a[(\bigint)lo + hi - i - 1]))
          @   && (\forall int i; hi<i && i<\old(hi);
          @              a[i] == \old(a[(\bigint)lo + hi - i - 1]))
          @   && (\forall int i; lo<=i && i<=hi;
          @              a[i] == \old(a[i]));
          @ assignable
          @   a[0 .. (\bigint)a.length-1];
          @ decreases (\bigint)hi+1-lo;
          @*/
        while (lo < hi) {
            Object t = a[lo];
            a[lo++] = a[hi];
            a[hi--] = t;
        }
    }

    /**
     * Returns the minimum acceptable run length for an array of the specified
     * length. Natural runs shorter than this will be extended with
     * {@link #binarySort}.
     *
     * Roughly speaking, the computation is:
     *
     *  If n < MIN_MERGE, return n (it's too small to bother with fancy stuff).
     *  Else if n is an exact power of 2, return MIN_MERGE/2.
     *  Else return an int k, MIN_MERGE/2 <= k <= MIN_MERGE, such that n/k
     *   is close to, but strictly less than, an exact power of 2.
     *
     * For the rationale, see listsort.txt.
     *
     * @param n the length of the array to be sorted
     * @return the length of the minimum run to be merged
     */

    /*@ private normal_behavior
      @ requires
      @   n >= MIN_MERGE;
      @ ensures
      @   \result >= MIN_MERGE/2;
      @*/
    private static int /*@ pure @*/ minRunLength(int n) {
        assert n >= 0;
        int r = 0;      // Becomes 1 if any 1 bits are shifted off
        /*@ loop_invariant n >= MIN_MERGE/2 && r >=0 && r<=1;
          @ decreases n;
          @ assignable \nothing;
          @*/
        while (n >= MIN_MERGE) {
            r |= (n & 1);
            n >>= 1;
        }
        return n + r;
    }

    /**
     * Pushes the specified run onto the pending-run stack.
     *
     * @param runBase index of the first element in the run
     * @param runLen  the number of elements in the run
     */

    /*@ private normal_behavior
      @ requires
      @      runLen > 0 && runLen <= a.length && runBase >= 0
      @   && (stackSize > 0  ==>
      @         runBase ==   (\bigint)this.runBase[(\bigint)stackSize-1]
      @                    +          this.runLen[(\bigint)stackSize-1])
      @   && ((\bigint)runLen + runBase <= a.length)
      @   && \dl_elemBiggerThanNext2(this.runLen, (\bigint)stackSize-4)
      @   && \dl_elemBiggerThanNext2(this.runLen, (\bigint)stackSize-3)
      @   && \dl_elemBiggerThanNext(this.runLen, (\bigint)stackSize-2)
      @   && \dl_elemLargerThanBound(this.runLen, (\bigint)stackSize-1, MIN_MERGE/2);
      @ ensures
      @      this.runBase[\old(stackSize)] == runBase
      @   && this.runLen[\old(stackSize)] == runLen
      @   && stackSize == (\bigint)\old(stackSize)+1;
      @ assignable
      @   this.runBase[stackSize], this.runLen[stackSize], this.stackSize;
      @*/
    private void pushRun(int runBase, int runLen) {
        this.runBase[stackSize] = runBase;
        this.runLen[stackSize] = runLen;
        stackSize++;
    }

    /**
     * Examines the stack of runs waiting to be merged and merges adjacent runs
     * until the stack invariants are reestablished:
     *
     *     1. runLen[i - 3] > runLen[i - 2] + runLen[i - 1]
     *     2. runLen[i - 2] > runLen[i - 1]
     *
     * This method is called each time a new run is pushed onto the stack,
     * so the invariants are guaranteed to hold for i < stackSize upon
     * entry to the method.
     */
    private void mergeCollapse() {
        while (stackSize > 1) {
            int n = stackSize - 2;
            if (n > 0 && runLen[n-1] <= runLen[n] + runLen[n+1]) {
                if (runLen[n - 1] < runLen[n + 1])
                    n--;
                mergeAt(n);
            } else if (runLen[n] <= runLen[n + 1]) {
                mergeAt(n);
            } else {
                break; // Invariant is established
            }
        }
    }
    
    /*@ private normal_behavior
      @ requires
      @      \dl_elemInv(runLen, (\bigint)stackSize-4, MIN_MERGE/2)
      @   && \dl_elemBiggerThanNext(runLen, (\bigint)stackSize-3)
      @   && stackSize > 0;
      @ ensures
      @    (\forall \bigint i; 0<=i && i<(\bigint)stackSize-2;
      @        \dl_elemInv(runLen, i, MIN_MERGE/2))
      @ && \dl_elemBiggerThanNext(runLen, (\bigint)stackSize-2)
      @ && (   (\sum int i; 0<=i && i<stackSize; (\bigint)runLen[i])
      @     == \old((\sum int i; 0<=i && i<stackSize; (\bigint)runLen[i])))
      @ && (runLen[(\bigint)stackSize-1] >= \old(runLen[(\bigint)stackSize-1]))
      @ && (0 < stackSize && stackSize <= \old(stackSize));
      @ assignable
      @   this.runBase[1 .. (\bigint)this.runBase.length-1],
      @   this.runLen[0 .. (\bigint)this.runLen.length-1],
      @   this.stackSize,
      @   this.tmp,
      @   this.tmp[0 .. (\bigint)tmp.length-1],
      @   this.minGallop,
      @   this.a[0 .. (\bigint)this.a.length-1];
      @*/
    private void newMergeCollapse() {
        /*@ loop_invariant
          @    (0 < stackSize && stackSize <= runLen.length)
          @ && (   (\sum int i; 0<=i && i<stackSize; (\bigint)runLen[i])
          @     == \old((\sum int i; 0<=i && i<stackSize; (\bigint)runLen[i])))
          @ && (\forall \bigint i; 0<=i && i<(\bigint)stackSize-4;
          @        \dl_elemInv(runLen, i, MIN_MERGE/2))
          @ && \dl_elemBiggerThanNext(runLen, (\bigint)stackSize-4)
          @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-3, MIN_MERGE/2)
          @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-2, MIN_MERGE/2)
          @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-1, 1)
          @ && (\forall \bigint i; 0<=i && i<(\bigint)stackSize-1;
          @        (\bigint)runBase[i] + runLen[i] == runBase[(\bigint)i+1])
          @ && (runLen[(\bigint)stackSize-1] >= \old(runLen[(\bigint)stackSize-1]))
          @ && (0 < stackSize && stackSize <= \old(stackSize))
          @ && (this.tmp != null && (tmp != \old(tmp) ==> \fresh(tmp)))
	  @ && (\typeof(tmp) == \type(Object[]) && \dl_inInt(minGallop));
          @ assignable
          @   this.runBase[1 .. (\bigint)this.runBase.length - 1],
          @   this.runLen[0 .. (\bigint)this.runLen.length-1],
          @   this.stackSize,
          @   this.tmp,
          @   this.tmp[0 .. (\bigint)this.tmp.length-1],
          @   this.minGallop,
          @   this.a[0 .. (\bigint)this.a.length-1];
          @ decreases stackSize;
          @*/
        while (stackSize > 1) {
            int n = stackSize - 2;
            if (     n > 0 && runLen[n-1] <= runLen[n] + runLen[n+1]
                || n-1 > 0 && runLen[n-2] <= runLen[n] + runLen[n-1]) {
                if (runLen[n-1] < runLen[n+1])
                    n--;
            } else if (n<0 || runLen[n] > runLen[n+1]) {
                break; // Invariant is established
            }
            mergeAt(n);
        }
    }

    /**
     * Merges all runs on the stack until only one remains.  This method is
     * called once, to complete the sort.
     */

    /*@ private normal_behavior
      @ requires
      @   stackSize > 0;
      @ ensures
      @   stackSize == 1;
      @*/
    private void mergeForceCollapse() {
        /*@ loop_invariant
          @    (0 < stackSize && stackSize <= runLen.length)
          @ && (   (\sum int i; 0<=i && i<stackSize; (\bigint)runLen[i])
          @     == \old((\sum int i; 0<=i && i<stackSize; (\bigint)runLen[i])))
          @ && (\forall \bigint i; 0<=i && i<(\bigint)stackSize-4;
          @        \dl_elemInv(runLen, i, MIN_MERGE/2))
          @ && \dl_elemBiggerThanNext(runLen, (\bigint)stackSize-4)
          @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-3, MIN_MERGE/2)
          @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-2, MIN_MERGE/2)
          @ && \dl_elemLargerThanBound(runLen, (\bigint)stackSize-1, 1)
          @ && (\forall \bigint i; 0<=i && i<(\bigint)stackSize-1;
          @        (\bigint)runBase[i] + runLen[i] == runBase[(\bigint)i+1])
          @ && (runLen[(\bigint)stackSize-1] >= \old(runLen[(\bigint)stackSize-1]))
          @ && (0 < stackSize && stackSize <= \old(stackSize))
          @ && (this.tmp != null && (tmp != \old(tmp) ==> \fresh(tmp)))
	  @ && (\typeof(tmp) == \type(Object[]) && \dl_inInt(minGallop));
          @ assignable
          @   this.runBase[1 .. (\bigint)this.runBase.length-1],
          @   this.runLen[0 .. (\bigint)this.runLen.length-1],
          @   this.stackSize,
          @   this.tmp,
          @   this.tmp[0 .. (\bigint)this.tmp.length-1],
          @   this.minGallop,
          @   this.a[0 .. (\bigint)this.a.length-1];
          @ decreases stackSize;
          @*/
        while (stackSize > 1) {
            int n = stackSize - 2;
            /*@ public normal_behavior
              @ requires
	      @   n == (\bigint)stackSize - 2;
	      @ ensures
	      @   (n>=0 && (n == (\bigint)stackSize - 2 || n == (\bigint)stackSize - 3));
              @ assignable \nothing;
	      @*/
	    {
            if (n > 0 && runLen[n - 1] < runLen[n + 1])
                n--;
	    }
            mergeAt(n);
        }
    }

    /**
     * Merges the two runs at stack indices i and i+1.  Run i must be
     * the penultimate or antepenultimate run on the stack.  In other words,
     * i must be equal to stackSize-2 or stackSize-3.
     *
     * @param i stack index of the first of the two runs to merge
     */

    /*@ private normal_behavior
      @ requires
      @      stackSize > 1 && i >= 0
      @   && (i == (\bigint)stackSize - 2 || i == (\bigint)stackSize - 3);
      @ ensures
      @      stackSize == (\bigint)\old(stackSize)-1
      @   && runLen[i] == \old((\bigint)runLen[i] + runLen[(\bigint)i+1])
      @   && (i == (\bigint)\old(stackSize)-3 ==>
      @         (  runLen [(\bigint)i+1] == \old(runLen [(\bigint)i+2])
      @          & runBase[(\bigint)i+1] == \old(runBase[(\bigint)i+2])))
      @   && (tmp != \old(tmp) ==> \fresh(tmp));
      @ assignable
      @   this.runBase[(\bigint)i+1 .. (\bigint)stackSize-2],
      @   this.runLen [i .. (\bigint)stackSize-2],
      @   this.stackSize,
      @   this.tmp,
      @   this.tmp[0 .. (\bigint)this.tmp.length-1],
      @   this.minGallop,
      @   this.a[0 .. (\bigint)this.a.length-1];
      @*/
    private void mergeAt(int i) {
        assert stackSize >= 2;
        assert i >= 0;
        assert i == stackSize - 2 || i == stackSize - 3;

        int base1 = runBase[i];
        int len1 = runLen[i];
        int base2 = runBase[i + 1];
        int len2 = runLen[i + 1];
        assert len1 > 0 && len2 > 0;
        assert base1 + len1 == base2;

        /*
         * Record the length of the combined runs; if i is the 3rd-last
         * run now, also slide over the last run (which isn't involved
         * in this merge).  The current run (i+1) goes away in any case.
         */
        runLen[i] = len1 + len2;
	/*@ normal_behavior
          @ ensures
          @      (i == (\bigint)stackSize-3 ==>
	  @         (   runLen[(\bigint)i+1]  == \old(runLen[(\bigint)i+2])
	  @          && runBase[(\bigint)i+1] == \old(runBase[(\bigint)i+2])))
	  @   &&
          @      (i == (\bigint)stackSize-2 ==>
	  @         (   runLen[(\bigint)i+1]  == \old(runLen[(\bigint)i+1])
	  @          && runBase[(\bigint)i+1] == \old(runBase[(\bigint)i+1])));
          @ assignable
          @   runBase[i+1], runLen[i+1];
          @*/
	{
        if (i == stackSize - 3) {
            runBase[i + 1] = runBase[i + 2];
            runLen[i + 1] = runLen[i + 2];
        }
	}
        stackSize--;

        /*
         * Find where the first element of run2 goes in run1. Prior elements
         * in run1 can be ignored (because they're already in place).
         */
        int k = gallopRight(a[base2], a, base1, len1, 0, c);
        assert k >= 0;
        base1 += k;
        len1 -= k;
        if (len1 == 0)
            return;

        /*
         * Find where the last element of run1 goes in run2. Subsequent elements
         * in run2 can be ignored (because they're already in place).
         */
        len2 = gallopLeft(a[base1 + len1 - 1], a, base2, len2, len2 - 1, c);
        assert len2 >= 0;
        if (len2 == 0)
            return;

        // Merge remaining runs, using tmp array with min(len1, len2) elements
        if (len1 <= len2)
            mergeLo(base1, len1, base2, len2);
        else
            mergeHi(base1, len1, base2, len2);
    }

    /**
     * Locates the position at which to insert the specified key into the
     * specified sorted range; if the range contains an element equal to key,
     * returns the index of the leftmost equal element.
     *
     * @param key the key whose insertion point to search for
     * @param a the array in which to search
     * @param base the index of the first element in the range
     * @param len the length of the range; must be > 0
     * @param hint the index at which to begin the search, 0 <= hint < n.
     *     The closer hint is to the result, the faster this method will run.
     * @param c the comparator used to order the range, and to search
     * @return the int k,  0 <= k <= n such that a[b + k - 1] < key <= a[b + k],
     *    pretending that a[b - 1] is minus infinity and a[b + n] is infinity.
     *    In other words, key belongs at index b + k; or in other words,
     *    the first k elements of a should precede key, and the last n - k
     *    should follow it.
     */

    /*@ private normal_behavior
      @ requires
      @   a != null && base >= 0 && len > 0 && hint < len && (\bigint)base + len <= a.length && hint >= 0;
      @ ensures
      @   0 <= \result && \result <= len;
      @*/
    private static int /*@ strictly_pure @*/ gallopLeft(/*@ nullable @*/ Object key, /*@ nullable @*/ Object[] a, int base, int len, int hint,
                                      Comparator/*<? super T>*/ c) {
        assert len > 0 && hint >= 0 && hint < len;
        int lastOfs = 0;
        int ofs = 1;
        if (c.compare(key, a[base + hint]) > 0) {
            // Gallop right until a[base+hint+lastOfs] < key <= a[base+hint+ofs]
            int maxOfs = len - hint;

            /*@ loop_invariant
              @    (0 < ofs && -1 <= lastOfs && lastOfs < ofs && lastOfs < maxOfs);
              @ assignable
              @   \strictly_nothing;
              @ decreases (\bigint)maxOfs-lastOfs;
              @*/
            while (ofs < maxOfs && c.compare(key, a[base + hint + ofs]) > 0) {
                lastOfs = ofs;
                ofs = (ofs << 1) + 1;
                if (ofs <= 0)   // int overflow
                    ofs = maxOfs;
            }
            if (ofs > maxOfs)
                ofs = maxOfs;

            // Make offsets relative to base
            lastOfs += hint;
            ofs += hint;
        } else { // key <= a[base + hint]
            // Gallop left until a[base+hint-ofs] < key <= a[base+hint-lastOfs]
            final int maxOfs = hint + 1;
            
	    /*@ loop_invariant
              @    (0 < ofs && -1 <= lastOfs && lastOfs < ofs && lastOfs < maxOfs);
              @ assignable
              @   \strictly_nothing;
              @ decreases (\bigint)maxOfs-lastOfs;
              @*/
            while (ofs < maxOfs && c.compare(key, a[base + hint - ofs]) <= 0) {
                lastOfs = ofs;
                ofs = (ofs << 1) + 1;
                if (ofs <= 0)   // int overflow
                    ofs = maxOfs;
            }
            if (ofs > maxOfs)
                ofs = maxOfs;

            // Make offsets relative to base
            int tmp = lastOfs;
            lastOfs = hint - ofs;
            ofs = hint - tmp;
        }
        assert -1 <= lastOfs && lastOfs < ofs && ofs <= len;

        /*
         * Now a[base+lastOfs] < key <= a[base+ofs], so key belongs somewhere
         * to the right of lastOfs but no farther right than ofs.  Do a binary
         * search, with invariant a[base + lastOfs - 1] < key <= a[base + ofs].
         */
        lastOfs++;
        
        /*@ loop_invariant 
           @      (lastOfs >= 0 && lastOfs <= ofs && ofs <= len)
	   @   && (lastOfs <= (ofs+lastOfs) >>> 1 && (ofs+lastOfs) >>> 1 <= ofs);
           @ decreases
	   @   ((\bigint)ofs - lastOfs) + 1, ofs;
           @ assignable
	   @   \strictly_nothing;
           @*/
        while (lastOfs < ofs) {
            int m = lastOfs + ((ofs - lastOfs) >>> 1);

            if (c.compare(key, a[base + m]) > 0)
                lastOfs = m + 1;  // a[base + m] < key
            else
                ofs = m;          // key <= a[base + m]
        }
        assert lastOfs == ofs;    // so a[base + ofs - 1] < key <= a[base + ofs]
        return ofs;
    }

    /**
     * Like gallopLeft, except that if the range contains an element equal to
     * key, gallopRight returns the index after the rightmost equal element.
     *
     * @param key the key whose insertion point to search for
     * @param a the array in which to search
     * @param base the index of the first element in the range
     * @param len the length of the range; must be > 0
     * @param hint the index at which to begin the search, 0 <= hint < n.
     *     The closer hint is to the result, the faster this method will run.
     * @param c the comparator used to order the range, and to search
     * @return the int k,  0 <= k <= n such that a[b + k - 1] <= key < a[b + k]
     */

    /*@ private normal_behavior
      @ requires
      @   a != null && base >= 0 && len > 0 && hint < len && (\bigint)base + len <= a.length && hint >= 0;
      @ ensures
      @   0 <= \result && \result <= len;
      @*/
    private static int /*@ strictly_pure @*/ gallopRight(/*@ nullable @*/ Object key, /*@ nullable @*/ Object[] a, int base, int len,
                                       int hint, Comparator/*<? super T>*/ c) {
        assert len > 0 && hint >= 0 && hint < len;

        int ofs = 1;
        int lastOfs = 0;
        if (c.compare(key, a[base + hint]) < 0) {
            // Gallop left until a[b+hint - ofs] <= key < a[b+hint - lastOfs]
            int maxOfs = hint + 1;

            /*@ loop_invariant
              @    (0 < ofs && -1 <= lastOfs && lastOfs < ofs && lastOfs < maxOfs);
              @ assignable
              @   \strictly_nothing;
              @ decreases (\bigint)maxOfs-lastOfs;
              @*/
            while (ofs < maxOfs && c.compare(key, a[base + hint - ofs]) < 0) {
                lastOfs = ofs;
                ofs = (ofs << 1) + 1;
                if (ofs <= 0)   // int overflow
                    ofs = maxOfs;
            }
            if (ofs > maxOfs)
                ofs = maxOfs;

            // Make offsets relative to b
            int tmp = lastOfs;
            lastOfs = hint - ofs;
            ofs = hint - tmp;
        } else { // a[b + hint] <= key
            // Gallop right until a[b+hint + lastOfs] <= key < a[b+hint + ofs]
            int maxOfs = len - hint;
            
	    /*@ loop_invariant
              @    (0 < ofs && -1 <= lastOfs && lastOfs < ofs && lastOfs < maxOfs);
              @ assignable
              @   \strictly_nothing;
              @ decreases (\bigint)maxOfs-lastOfs;
              @*/
            while (ofs < maxOfs && c.compare(key, a[base + hint + ofs]) >= 0) {
                lastOfs = ofs;
                ofs = (ofs << 1) + 1;
                if (ofs <= 0)   // int overflow
                    ofs = maxOfs;
            }
            if (ofs > maxOfs)
                ofs = maxOfs;

            // Make offsets relative to b
            lastOfs += hint;
            ofs += hint;
        }
        assert -1 <= lastOfs && lastOfs < ofs && ofs <= len;

        /*
         * Now a[b + lastOfs] <= key < a[b + ofs], so key belongs somewhere to
         * the right of lastOfs but no farther right than ofs.  Do a binary
         * search, with invariant a[b + lastOfs - 1] <= key < a[b + ofs].
         */
        lastOfs++;
        
        /*@ loop_invariant 
           @      (lastOfs >= 0 && lastOfs <= ofs && ofs <= len)
	   @   && (lastOfs <= (ofs+lastOfs) >>> 1 && (ofs+lastOfs) >>> 1 <= ofs);
           @ decreases
	   @   ((\bigint)ofs - lastOfs) + 1, ofs;
           @ assignable
	   @   \strictly_nothing;
           @*/
        while (lastOfs < ofs) {
            int m = lastOfs + ((ofs - lastOfs) >>> 1);

            if (c.compare(key, a[base + m]) < 0)
                ofs = m;          // key < a[b + m]
            else
                lastOfs = m + 1;  // a[b + m] <= key
        }
        assert lastOfs == ofs;    // so a[b + ofs - 1] <= key < a[b + ofs]
        return ofs;
    }

    /**
     * Merges two adjacent runs in place, in a stable fashion.  The first
     * element of the first run must be greater than the first element of the
     * second run (a[base1] > a[base2]), and the last element of the first run
     * (a[base1 + len1-1]) must be greater than all elements of the second run.
     *
     * For performance, this method should be called only when len1 <= len2;
     * its twin, mergeHi should be called if len1 >= len2.  (Either method
     * may be called if len1 == len2.)
     *
     * @param base1 index of first element in first run to be merged
     * @param len1  length of first run to be merged (must be > 0)
     * @param base2 index of first element in second run to be merged
     *        (must be aBase + aLen)
     * @param len2  length of second run to be merged (must be > 0)
     */

    /*@ private normal_behavior
      @ requires
      @      (base1 >= 0 && len1 > 0 && len2 > 0 && len1 <= len2)
      @   && ((\bigint)base1 + len1 == base2 && (\bigint)base2 + len2 <= a.length);
      @ ensures
      @   (tmp != \old(tmp) ==> \fresh(tmp));
      @ assignable
      @   this.tmp,
      @   this.tmp[0 .. (\bigint)this.tmp.length-1],
      @   this.minGallop,
      @   this.a[0 .. (\bigint)this.a.length-1];
      @*/
    private void mergeLo(int base1, int len1, int base2, int len2) {
        assert len1 > 0 && len2 > 0 && base1 + len1 == base2;

        // Copy first run into temp array
        Object[] a = this.a; // For performance
        Object[] tmp = ensureCapacity(len1);
        System.arraycopy(a, base1, tmp, 0, len1);

        int cursor1 = 0;       // Indexes into tmp array
        int cursor2 = base2;   // Indexes int a
        int dest = base1;      // Indexes int a

        // Move first element of second run and deal with degenerate cases
        a[dest++] = a[cursor2++];

	if (--len2 == 0) {
	    System.arraycopy(tmp, cursor1, a, dest, len1);
	    return;
	}
	if (len1 == 1) {
	    System.arraycopy(a, cursor2, a, dest, len2);
	    a[dest + len2] = tmp[cursor1]; // Last elt of run 1 to end of merge
	    return;
	}
	
        Comparator/*<? super T>*/ c = this.c;  // Use local variable for performance
        int minGallop = this.minGallop;    //  "    "       "     "      "

      /*@ public normal_behavior
	@ requires true;
	@ ensures len1 == 0 
	@   || ( len1 == 1 && len2 > 0 && cursor2 >= 0 && (\bigint)cursor2 + (\bigint)len2 <= a.length && dest >= 0
	@        && (\bigint)dest + (\bigint)len2 >= 0 && (\bigint)dest + (\bigint)len2 < a.length && cursor1 < a.length && 
	@           cursor1 < \old(len1) && cursor1 >=0) 
	@   || ( len2 == 0 && len1 > 1 && cursor1 >=0 && (\bigint)cursor1 + (\bigint)len1 <= \old(len1) 
	@        && (\bigint)dest + (\bigint)len1 <= a.length && dest >= 0);
	@ assignable this.a[0 .. (\bigint)this.a.length-1];
	@*/
      {
      outer:
	/*@ loop_invariant 
	  @    cursor1 >= 0 && 
	  @    cursor1 <= tmp.length && 
	  @    cursor2 >= base2      && 
	  @    dest >=0              &&  len1 > 1  &&  len2 > 0  && 
	  @    (\bigint)cursor1 + (\bigint)len1 == \old(len1)    &&
	  @    (\bigint)cursor2 + (\bigint)len2 == (\bigint)base2 + (\bigint)\old(len2) &&
	  @    (\bigint)dest + len1 == cursor2;
	  @ decreases a.length - dest;
	  @ assignable 
	  @   this.a[0 .. (\bigint)this.a.length-1];
	  @*/
        while (true) {
            int count1 = 0; // Number of times in a row that first run won
            int count2 = 0; // Number of times in a row that second run won

            /*
             * Do the straightforward thing until (if ever) one run starts
             * winning consistently.
             */
	    /*@ loop_invariant 
	      @    cursor1 >= 0 && 
	      @    cursor1 <= tmp.length && // maybe remove
	      @    cursor2 >= base2      && 
	      @    dest >=0              &&  len1 > 1  &&  len2 > 0  && 
	      @    (\bigint)cursor1 + (\bigint)len1 == \old(len1)    &&
	      @    (\bigint)cursor2 + (\bigint)len2 == (\bigint)base2 + (\bigint)\old(len2) &&
	      @    (\bigint)dest + len1 == cursor2;
	      @ decreases len1, len2;
	      @ assignable this.a[0 .. (\bigint)this.a.length-1];
	      @*/
            do {
		assert len1 > 1 && len2 > 0;
                if (c.compare(a[cursor2], tmp[cursor1]) < 0) {
                    a[dest++] = a[cursor2++];
                    count2++;
                    count1 = 0;
                    if (--len2 == 0)
                        break outer;
                } else {
                    a[dest++] = tmp[cursor1++];
                    count1++;
                    count2 = 0;
                    if (--len1 == 1)
                        break outer;
                }
            } while ((count1 | count2) < minGallop);

            /*
             * One run is winning so consistently that galloping may be a
             * huge win. So try that, and continue galloping until (if ever)
             * neither run appears to be winning consistently anymore.
             */
	     /*@ loop_invariant 
	      @    cursor1 >= 0 &&  
	      @    cursor2 >= base2      && 
	      @    dest >=0              &&  len1 > 1  &&  len2 > 0  && 
	      @    (\bigint)cursor1 + (\bigint)len1 == \old(len1)    &&
	      @    (\bigint)cursor2 + (\bigint)len2 == (\bigint)base2 + (\bigint)\old(len2) &&
	      @    (\bigint)dest + len1 == cursor2;
	      @ decreases len1, len2;
	      @ assignable this.a[0 .. (\bigint)this.a.length-1];
	      @*/
            do {
                assert len1 > 1 && len2 > 0;
                count1 = gallopRight(a[cursor2], tmp, cursor1, len1, 0, c);
                if (count1 != 0) {
                    System.arraycopy(tmp, cursor1, a, dest, count1);
                    dest += count1;
                    cursor1 += count1;
                    len1 -= count1;
                    if (len1 <= 1) // len1 == 1 || len1 == 0
                        break outer;
                }
                a[dest++] = a[cursor2++];
                if (--len2 == 0)
                    break outer;

                count2 = gallopLeft(tmp[cursor1], a, cursor2, len2, 0, c);
                if (count2 != 0) {
                    System.arraycopy(a, cursor2, a, dest, count2);
                    dest += count2;
                    cursor2 += count2;
                    len2 -= count2;
                    if (len2 == 0)
                        break outer;
                }
                a[dest++] = tmp[cursor1++];
                if (--len1 == 1)
                    break outer;
                minGallop--;
            } while (count1 >= MIN_GALLOP | count2 >= MIN_GALLOP);
            if (minGallop < 0)
                minGallop = 0;
            minGallop += 2;  // Penalize for leaving gallop mode
        }  // End of "outer" loop
      }
	
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures this.minGallop >= 1 && \dl_inInt(minGallop) && \dl_inInt(this.minGallop);
	  @ assignable this.minGallop;
	  @*/
      {
         this.minGallop = minGallop < 1 ? 1 : minGallop;  // Write back to field
      }
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures true;
	  @ assignable this.a[0 .. (\bigint)this.a.length-1];
	  @*/
      {
        if (len1 == 1) {
            assert len2 > 0;
            System.arraycopy(a, cursor2, a, dest, len2);
            a[dest + len2] = tmp[cursor1]; //  Last elt of run 1 to end of merge
        } else if (len1 == 0) {
//	    throw new IllegalArgumentException(
//                "Comparison method violates its general contract!");
        } else {
            assert len2 == 0;
            assert len1 > 1;
            System.arraycopy(tmp, cursor1, a, dest, len1);
        }
      }
    }

    /**
     * Like mergeLo, except that this method should be called only if
     * len1 >= len2; mergeLo should be called if len1 <= len2.  (Either method
     * may be called if len1 == len2.)
     *
     * @param base1 index of first element in first run to be merged
     * @param len1  length of first run to be merged (must be > 0)
     * @param base2 index of first element in second run to be merged
     *        (must be aBase + aLen)
     * @param len2  length of second run to be merged (must be > 0)
     */

    /*@ private normal_behavior
      @ requires
      @      (base1 >= 0 && len1 > 0 && len2 > 0 && len1 >= len2)
      @   && ((\bigint)base1 + len1 == base2 && (\bigint)base2 + len2 <= a.length);
      @ ensures
      @   (tmp != \old(tmp) ==> \fresh(tmp));
      @ assignable
      @   this.tmp,
      @   this.tmp[0 .. (\bigint)this.tmp.length-1],
      @   this.minGallop,
      @   this.a[0 .. (\bigint)this.a.length-1];
      @*/
    private void mergeHi(int base1, int len1, int base2, int len2) {
        assert len1 > 0 && len2 > 0 && base1 + len1 == base2;

        // Copy second run into temp array
        Object[] a = this.a; // For performance
        Object[] tmp = ensureCapacity(len2);
        System.arraycopy(a, base2, tmp, 0, len2);

        int cursor1 = base1 + len1 - 1;  // Indexes into a
        int cursor2 = len2 - 1;          // Indexes into tmp array
        int dest = base2 + len2 - 1;     // Indexes into a

        // Move last element of first run and deal with degenerate cases
        a[dest--] = a[cursor1--];
        if (--len1 == 0) {
            System.arraycopy(tmp, 0, a, dest - (len2 - 1), len2);
            return;
        }
        if (len2 == 1) {
            dest -= len1;
            cursor1 -= len1;
            System.arraycopy(a, cursor1 + 1, a, dest + 1, len1);
            a[dest] = tmp[cursor2];
            return;
        }

        Comparator/*<? super T>*/ c = this.c;  // Use local variable for performance
        int minGallop = this.minGallop;    //  "    "       "     "      "
      /*@ public normal_behavior
	@ requires true;
	@ ensures len2 == 0 
	@   || (   len2 == 1 && len1 > 0 && dest >= len1
	@       && dest < a.length && cursor2 < \old(len2)
	@       && len1 <= (\bigint)cursor1 + 1 && cursor1 < a.length)
	@   || (   len1 == 0 && len2 > 1  && len2 <= \old(len2)
        @       && len2 <= (\bigint)dest + 1 && dest < a.length);
	@ assignable this.a[0 .. (\bigint)this.a.length-1];
	@*/
       {
       outer:
	/*@ loop_invariant
	@    0 < len1 && len1 < \old(len1)
	@ && 1 < len2 && len2 <= \old(len2)
	@ && (\bigint)cursor1 + 1 == (\bigint)base1 + len1
	@ && (\bigint)cursor2 + 1 == len2
	@ && dest == (\bigint)cursor1 + len2;
	@ decreases dest;
	@ assignable this.a[0 .. (\bigint)this.a.length-1];
	@*/
        while (true) {
            int count1 = 0; // Number of times in a row that first run won
            int count2 = 0; // Number of times in a row that second run won
	    //@ ghost int dest_loop = dest;

            /*
             * Do the straightforward thing until (if ever) one run
             * appears to win consistently.
             */
	    /*@ loop_invariant
	    @    0 < len1 && len1 < \old(len1)
	    @ && 1 < len2 && len2 <= \old(len2)
	    @ && (dest < dest_loop)
	    @ && (\bigint)cursor1 + 1 == (\bigint)base1 + len1
	    @ && (\bigint)cursor2 + 1 == len2
	    @ && dest == (\bigint)cursor1 + len2; 
	    @ decreases dest;
	    @ assignable this.a[0 .. (\bigint)this.a.length-1];
	    @*/
            do {
                assert len1 > 0 && len2 > 1;
                if (c.compare(tmp[cursor2], a[cursor1]) < 0) {
                    a[dest--] = a[cursor1--];
                    count1++;
                    count2 = 0;
                    if (--len1 == 0)
                        break outer;
                } else {
                    a[dest--] = tmp[cursor2--];
                    count2++;
                    count1 = 0;
                    if (--len2 == 1)
                        break outer;
                }
            } while ((count1 | count2) < minGallop);

            /*
             * One run is winning so consistently that galloping may be a
             * huge win. So try that, and continue galloping until (if ever)
             * neither run appears to be winning consistently anymore.
             */
	    /*@ loop_invariant
	    @    0 < len1 && len1 < \old(len1)
	    @ && 1 < len2 && len2 <= \old(len2)
	    @ && (dest < dest_loop)
	    @ && (\bigint)cursor1 + 1 == (\bigint)base1 + len1
	    @ && (\bigint)cursor2 + 1 == len2
	    @ && dest == (\bigint)cursor1 + len2;
	    @ decreases dest;
	    @ assignable this.a[0 .. (\bigint)this.a.length-1];
	    @*/
	    do {
                assert len1 > 0 && len2 > 1;
                count1 = len1 - gallopRight(tmp[cursor2], a, base1, len1, len1 - 1, c);
                if (count1 != 0) { //join
                    dest -= count1;
                    cursor1 -= count1;
                    len1 -= count1;
                    System.arraycopy(a, cursor1 + 1, a, dest + 1, count1);
                    if (len1 == 0)
                        break outer;
                } // join end
                a[dest--] = tmp[cursor2--];
                if (--len2 == 1)
                    break outer;

                count2 = len2 - gallopLeft(a[cursor1], tmp, 0, len2, len2 - 1, c);
                if (count2 != 0) {
                    dest -= count2;
                    cursor2 -= count2;
                    len2 -= count2;
                    System.arraycopy(tmp, cursor2 + 1, a, dest + 1, count2);
                    if (len2 <= 1)  // len2 == 1 || len2 == 0
                        break outer;
                }
                a[dest--] = a[cursor1--];
                if (--len1 == 0)
                    break outer;
                minGallop--;
            } while (count1 >= MIN_GALLOP | count2 >= MIN_GALLOP);
            if (minGallop < 0)
                minGallop = 0;
            minGallop += 2;  // Penalize for leaving gallop mode
        }  // End of "outer" loop
       }
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures this.minGallop >= 1 && \dl_inInt(minGallop) && \dl_inInt(this.minGallop);
	  @ assignable this.minGallop;
	  @*/
	{
        this.minGallop = minGallop < 1 ? 1 : minGallop;  // Write back to field
	}
	
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures true;
	  @ assignable this.a[0 .. (\bigint)this.a.length-1];
	  @*/
        { if (len2 == 1) {
            assert len1 > 0;
            dest -= len1;
            cursor1 -= len1;
            System.arraycopy(a, cursor1 + 1, a, dest + 1, len1);
            a[dest] = tmp[cursor2];  // Move first elt of run2 to front of merge
        } else if (len2 == 0) {
//		throw new IllegalArgumentException(
//                "Comparison method violates its general contract!");
        } else {
            assert len1 == 0;
            assert len2 > 0;
            System.arraycopy(tmp, 0, a, dest - (len2 - 1), len2);
	} }
    }

    /**
     * Ensures that the external array tmp has at least the specified
     * number of elements, increasing its size if necessary.  The size
     * increases exponentially to ensure amortized linear time complexity.
     *
     * @param minCapacity the minimum required capacity of the tmp array
     * @return tmp, whether or not it grew
     */

    /*@ private normal_behavior
      @ requires
      @   minCapacity >= 0 && a.length / 2 >= minCapacity;
      @ ensures
      @      (\result == tmp && tmp.length >= minCapacity)
      @   && (tmp != \old(tmp) ==> \fresh(tmp)) 
      @   && (\result != null);
      @ assignable
      @   this.tmp;
      @*/
    private /*@ nullable @*/ Object[] ensureCapacity(int minCapacity) {
        if (tmp.length < minCapacity) {
            // Compute smallest power of 2 > minCapacity
            int newSize = minCapacity;
            /*@ public normal_behavior
              @ requires newSize == minCapacity;
              @ ensures newSize >= minCapacity;
              @ assignable \nothing;
              @*/
            {
            newSize |= newSize >> 1;
            newSize |= newSize >> 2;
            newSize |= newSize >> 4;
            newSize |= newSize >> 8;
            newSize |= newSize >> 16;
            newSize++;

            if (newSize < 0) // Not bloody likely!
                newSize = minCapacity;
            else
                newSize = Math.min(newSize, a.length >>> 1);
            }

            Object[] newArray = (Object[]) new Object[newSize];
            tmp = newArray;
        }
        return tmp;
    }
    /**
     * Checks that fromIndex and toIndex are in range, and throws an
     * appropriate exception if they aren't.
     *
     * @param arrayLen the length of the array
     * @param fromIndex the index of the first element of the range
     * @param toIndex the index after the last element of the range
     * @throws IllegalArgumentException if fromIndex > toIndex
     * @throws ArrayIndexOutOfBoundsException if fromIndex < 0
     *         or toIndex > arrayLen
     */

    /*@ private normal_behavior
      @ requires
      @   0 <= fromIndex && fromIndex <= toIndex && toIndex <= arrayLen;
      @ assignable
      @   \nothing;
      @*/
    private static void rangeCheck(int arrayLen, int fromIndex, int toIndex) {
        if (fromIndex > toIndex)
            throw new IllegalArgumentException("fromIndex(" + fromIndex +
                       ") > toIndex(" + toIndex+")");
        if (fromIndex < 0)
            throw new ArrayIndexOutOfBoundsException(fromIndex);
        if (toIndex > arrayLen)
            throw new ArrayIndexOutOfBoundsException(toIndex);
    }
}
