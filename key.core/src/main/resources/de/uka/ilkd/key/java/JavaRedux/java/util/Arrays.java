package java.util;

// Most method contracts here are tested against an example implementation in examples/redux/arrays to make sure that they are satisfiable.
// If you edit this or the other file, make sure to reflect the changes.
public final class Arrays {

    /*@ public normal_behavior
      @ ensures \invariant_for(\result);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static java.util.ArrayList asList(int[] arr);

    /*@ public normal_behavior
      @ ensures \invariant_for(\result);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
    public static java.util.ArrayList asList(char[] arr);

    /*@ public normal_behavior
      @ ensures \fresh(\result) && \fresh(\result.*);
      @ ensures \invariant_for(\result);
      @ ensures (\forall \bigint i; 0 <= i && i < \result.seq.length; ((String)\result.seq[i]) != null);
      @ assignable \nothing;
      @*/
    public static java.util.ArrayList asList(java.lang.String str);

    /*@ public normal_behavior
      @ ensures \fresh(\result) && \fresh(\result.*);
      @ ensures \invariant_for(\result);
      @ ensures (\forall \bigint i; 0 <= i && i < \result.seq.length; ((String)\result.seq[i]) != null);
      @ assignable \nothing;
      @*/
    public static java.util.ArrayList asList(java.lang.String[] arr);

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @ 	\result[i] == (i < original.length ? original[i] : false)
      @ );
      @ assignable \nothing;
      @*/
    public static boolean[] copyOf(boolean[] original, int newLength);

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @ 	\result[i] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static byte[] copyOf(byte[] original, int newLength);

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @ 	\result[i] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static char[] copyOf(char[] original, int newLength);

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @ 	\result[i] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static int[] copyOf(int[] original, int newLength);

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @ 	\result[i] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static short[] copyOf(short[] original, int newLength);

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @ 	\result[i] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static long[] copyOf(long[] original, int newLength);

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @     i < original.length ?
      @         Float._isSame(\result[i], original[i]) :
      @         \result[i] == 0.0f
      @ );
      @ assignable \nothing;
      @*/
    public static float[] copyOf(float[] original, int newLength);

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @     i < original.length ?
      @         Double._isSame(\result[i], original[i]) :
      @         \result[i] == 0.0d
      @ );
      @ assignable \nothing;
      @*/
    public static double[] copyOf(double[] original, int newLength);

    /*@ public normal_behavior
      @ requires 0 <= from <= to && from <= original.length;
      @ ensures \fresh(\result) && \result.length == to - from;
      @ ensures (\forall \bigint i; from <= i && i < to;
      @ 	\result[i - from] == (i < original.length ? original[i] : false)
      @ );
      @ assignable \nothing;
      @*/
    public static boolean[] copyOfRange(boolean[] original, int from, int to);

    /*@ public normal_behavior
      @ requires 0 <= from <= to && from <= original.length;
      @ ensures \fresh(\result) && \result.length == to - from;
      @ ensures (\forall \bigint i; from <= i && i < to;
      @ 	\result[i - from] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static char[] copyOfRange(char[] original, int from, int to);

    /*@ public normal_behavior
      @ requires 0 <= from <= to && from <= original.length;
      @ ensures \fresh(\result) && \result.length == to - from;
      @ ensures (\forall \bigint i; from <= i && i < to;
      @ 	\result[i - from] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static short[] copyOfRange(short[] original, int from, int to);

    /*@ public normal_behavior
      @ requires 0 <= from <= to && from <= original.length;
      @ ensures \fresh(\result) && \result.length == to - from;
      @ ensures (\forall \bigint i; from <= i && i < to;
      @ 	\result[i - from] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static int[] copyOfRange(int[] original, int from, int to);

    /*@ public normal_behavior
      @ requires 0 <= from <= to && from <= original.length;
      @ ensures \fresh(\result) && \result.length == to - from;
      @ ensures (\forall \bigint i; from <= i && i < to;
      @ 	\result[i - from] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static long[] copyOfRange(long[] original, int from, int to);

    /*@ public normal_behavior
      @ requires 0 <= from <= to && from <= original.length;
      @ ensures \fresh(\result) && \result.length == to - from;
      @ ensures (\forall \bigint i; from <= i && i < to;
      @     i < original.length ?
      @         Float._isSame(\result[i - from], original[i]) :
      @         \result[i - from] == 0.0f
      @ );
      @ assignable \nothing;
      @*/
    public static float[] copyOfRange(float[] original, int from, int to);

    /*@ public normal_behavior
      @ requires 0 <= from <= to && from <= original.length;
      @ ensures \fresh(\result) && \result.length == to - from;
      @ ensures (\forall \bigint i; from <= i && i < to;
      @     i < original.length ?
      @         Double._isSame(\result[i], original[i - from]) :
      @         \result[i - from] == 0.0d
      @ );
      @ assignable \nothing;
      @*/
    public static double[] copyOfRange(double[] original, int from, int to);

    /*@ public normal_behavior
      @ ensures \result <==> (
      @     a == a2 ||
      @     (a != null && a2 != null && a.length == a2.length &&
      @         (\forall \bigint j; 0 <= j && j < a.length; a[j] == a2[j]))
      @ );
      @ assignable \strictly_nothing;
      @*/
    public static boolean equals(/*@ nullable */ byte[] a, /*@ nullable */ byte[] a2);

    /*@ public normal_behavior
      @ ensures \result <==> (
      @     a == a2 ||
      @     (a != null && a2 != null && a.length == a2.length &&
      @         (\forall \bigint j; 0 <= j && j < a.length; a[j] == a2[j]))
      @ );
      @ assignable \strictly_nothing;
      @*/
    public static boolean equals(/*@ nullable */ int[] a, /*@ nullable */ int[] a2);

    /*@ public normal_behavior
      @ ensures \result <==> (
      @     a == a2 ||
      @     (a != null && a2 != null && a.length == a2.length &&
      @         (\forall \bigint j; 0 <= j && j < a.length; a[j] == a2[j]))
      @ );
      @ assignable \strictly_nothing;
      @*/
    public static boolean equals(/*@ nullable */ short[] a, /*@ nullable */ short[] a2);

    /*@ public normal_behavior
      @ ensures \result <==> (
      @     a == a2 ||
      @     (a != null && a2 != null && a.length == a2.length &&
      @         (\forall \bigint j; 0 <= j && j < a.length; a[j] == a2[j]))
      @ );
      @ assignable \strictly_nothing;
      @*/
    public static boolean equals(/*@ nullable */ long[] a, /*@ nullable */ long[] a2);

    /*@ public normal_behavior
      @ ensures \result <==> (
      @     a == a2 ||
      @     (a != null && a2 != null && a.length == a2.length &&
      @         (\forall \bigint j; 0 <= j && j < a.length; a[j] == a2[j]))
      @ );
      @ assignable \strictly_nothing;
      @*/
    public static boolean equals(/*@ nullable */ char[] a, /*@ nullable */ char[] a2);

    // Double and float equals are left out since they use *bitwise* equality

    /*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
    public static void fill(boolean[] a, boolean val);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void fill(boolean[] a, int fromIndex, int toIndex, boolean val);

    /*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
    public static void fill(int[] a, int val);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void fill(int[] a, int fromIndex, int toIndex, int val);

    /*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
    public static void fill(long[] a, long val);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void fill(long[] a, int fromIndex, int toIndex, long val);

    /*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
    public static void fill(byte[] a, byte val);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void fill(byte[] a, int fromIndex, int toIndex, byte val);

    /*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length;
      @     Double._isSame(a[i], val)
      @ );
      @ assignable a[*];
      @*/
    public static void fill(double[] a, double val);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex;
      @     Double._isSame(a[i], val)
      @ );
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void fill(double[] a, int fromIndex, int toIndex, double val);

    /*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length;
      @     Float._isSame(a[i], val)
      @ );
      @ assignable a[*];
      @*/
    public static void fill(float[] a, float val);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex;
      @     Float._isSame(a[i], val)
      @ );
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void fill(float[] a, int fromIndex, int toIndex, float val);

    /*@ public normal_behavior
      @ // Sorted ascending
      @ ensures (\forall \bigint i; 0 <= i < a.length - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; 0 <= i < a.length;
      @     (\forall \bigint j; i <= j < a.length; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; 0 <= i < a.length; a[i] == e) ==
      @         (\num_of \bigint i; 0 <= i < a.length; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(0, a.length, a), \old(\dl_seq_def_workaround(0, a.length, a)));
      @ assignable a[*];
      @*/
    public static void sort(int[] a);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ // Sorted ascending
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex;
      @     (\forall \bigint j; i <= j < toIndex; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; fromIndex <= i < toIndex; a[i] == e) ==
      @         (\num_of \bigint i; fromIndex <= i < toIndex; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(fromIndex, toIndex, a), \old(\dl_seq_def_workaround(fromIndex, toIndex, a)));
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void sort(int[] a, int fromIndex, int toIndex);

    /*@ public normal_behavior
      @ // Sorted ascending
      @ ensures (\forall \bigint i; 0 <= i < a.length - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; 0 <= i < a.length;
      @     (\forall \bigint j; i <= j < a.length; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; 0 <= i < a.length; a[i] == e) ==
      @         (\num_of \bigint i; 0 <= i < a.length; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(0, a.length, a), \old(\dl_seq_def_workaround(0, a.length, a)));
      @ assignable a[*];
      @*/
    public static void sort(short[] a);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ // Sorted ascending
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex;
      @     (\forall \bigint j; i <= j < toIndex; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; fromIndex <= i < toIndex; a[i] == e) ==
      @         (\num_of \bigint i; fromIndex <= i < toIndex; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(fromIndex, toIndex, a), \old(\dl_seq_def_workaround(fromIndex, toIndex, a)));
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void sort(short[] a, int fromIndex, int toIndex);

    /*@ public normal_behavior
      @ // Sorted ascending
      @ ensures (\forall \bigint i; 0 <= i < a.length - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; 0 <= i < a.length;
      @     (\forall \bigint j; i <= j < a.length; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; 0 <= i < a.length; a[i] == e) ==
      @         (\num_of \bigint i; 0 <= i < a.length; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(0, a.length, a), \old(\dl_seq_def_workaround(0, a.length, a)));
      @ assignable a[*];
      @*/
    public static void sort(long[] a);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ // Sorted ascending
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex;
      @     (\forall \bigint j; i <= j < toIndex; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; fromIndex <= i < toIndex; a[i] == e) ==
      @         (\num_of \bigint i; fromIndex <= i < toIndex; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(fromIndex, toIndex, a), \old(\dl_seq_def_workaround(fromIndex, toIndex, a)));
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void sort(long[] a, int fromIndex, int toIndex);

    /*@ public normal_behavior
      @ // Sorted ascending
      @ ensures (\forall \bigint i; 0 <= i < a.length - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; 0 <= i < a.length;
      @     (\forall \bigint j; i <= j < a.length; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; 0 <= i < a.length; a[i] == e) ==
      @         (\num_of \bigint i; 0 <= i < a.length; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(0, a.length, a), \old(\dl_seq_def_workaround(0, a.length, a)));
      @ assignable a[*];
      @*/
    public static void sort(byte[] a);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ // Sorted ascending
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex;
      @     (\forall \bigint j; i <= j < toIndex; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; fromIndex <= i < toIndex; a[i] == e) ==
      @         (\num_of \bigint i; fromIndex <= i < toIndex; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(fromIndex, toIndex, a), \old(\dl_seq_def_workaround(fromIndex, toIndex, a)));
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void sort(byte[] a, int fromIndex, int toIndex);

    /*@ public normal_behavior
      @ // Sorted ascending
      @ ensures (\forall \bigint i; 0 <= i < a.length - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; 0 <= i < a.length;
      @     (\forall \bigint j; i <= j < a.length; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; 0 <= i < a.length; a[i] == e) ==
      @         (\num_of \bigint i; 0 <= i < a.length; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(0, a.length, a), \old(\dl_seq_def_workaround(0, a.length, a)));
      @ assignable a[*];
      @*/
    public static void sort(char[] a);

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ // Sorted ascending
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex - 1;
      @     a[i] <= a[i + 1]
      @ );
      @ // Sorted ascending (transitive)
      @ ensures (\forall \bigint i; fromIndex <= i < toIndex;
      @     (\forall \bigint j; i <= j < toIndex; a[i] <= a[j])
      @ );
      @ // Permutation property (num_of)
      @ ensures (\forall int e; true;
      @     (\num_of \bigint i; fromIndex <= i < toIndex; a[i] == e) ==
      @         (\num_of \bigint i; fromIndex <= i < toIndex; \old(a[i]) == e)
      @ );
      @ // Permutation property (seqPerm)
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(fromIndex, toIndex, a), \old(\dl_seq_def_workaround(fromIndex, toIndex, a)));
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void sort(char[] a, int fromIndex, int toIndex);
}