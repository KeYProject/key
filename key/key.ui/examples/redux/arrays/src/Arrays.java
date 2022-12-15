// This file serves as a regression test for the redux file java.util.Arrays.
// If you edit this or the other file, make sure to reflect the changes.
public final class Arrays {
    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void fill(int[] a, int fromIndex, int toIndex, int val) {
        /*@ loop_invariant fromIndex <= i <= toIndex;
          @ loop_invariant (\forall \bigint j; fromIndex <= j && j < i; a[j] == val);
          @ assignable a[fromIndex..toIndex - 1];
          @ decreases toIndex - i;
          @*/
        for (int i = fromIndex; i < toIndex; i++)
            a[i] = val;
    }

    /*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
    public static void fill(int[] a, int val) {
        fill(a, 0, a.length, val);
    }

    /*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex;
      @     Float._isSame(a[i], val)
      @ );
      @ assignable a[fromIndex..toIndex - 1];
      @*/
    public static void fill(float[] a, int fromIndex, int toIndex, float val) {
        /*@ loop_invariant fromIndex <= i <= toIndex;
          @ loop_invariant (\forall \bigint j; fromIndex <= j && j < i;
          @     Float._isSame(a[j], val)
          @ );
          @ assignable a[fromIndex..toIndex - 1];
          @ decreases toIndex - i;
          @*/
        for (int i = fromIndex; i < toIndex; i++)
            a[i] = val;
    }

    /*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length;
      @     Float._isSame(a[i], val)
      @ );
      @ assignable a[*];
      @*/
    public static void fill(float[] a, float val) {
        fill(a, 0, a.length, val);
    }

    /*@ public normal_behavior
      @ ensures \result <==> (
      @     a == a2 ||
      @     (a != null && a2 != null && a.length == a2.length &&
      @         (\forall \bigint j; 0 <= j && j < a.length; a[j] == a2[j]))
      @ );
      @ assignable \strictly_nothing;
      @*/
    public static boolean equals(/*@ nullable */ byte[] a, /*@ nullable */ byte[] a2) {
        if (a == a2)
            return true;
        if (a == null || a2 == null)
            return false;

        int length = a.length;
        if (a2.length != length)
            return false;

        /*@ loop_invariant 0 <= i <= length;
          @ loop_invariant (\forall \bigint j; 0 <= j && j < i; a[j] == a2[j]);
          @ assignable \strictly_nothing;
          @ decreases length - i;
          @*/
        for (int i = 0; i < length; ++i) {
            if (a[i] != a2[i]) {
                return false;
            }
        }

        return true;
    }

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
    public static float[] copyOf(float[] original, int newLength) {
        //@ assert 0.0f == 0.0f;
        float[] copy = new float[newLength];
        int l = Math.min(original.length, newLength);
        /*@ loop_invariant 0 <= i <= l;
          @ loop_invariant (\forall \bigint j; 0 <= j && j < i;
          @     Float._isSame(copy[j], original[j])
          @ );
          @ assignable copy[0..l - 1];
          @ decreases l - i;
          @*/
        for (int i = 0; i < l; ++i) {
            copy[i] = original[i];
        }
        return copy;
    }

    /*@ public normal_behavior
      @ requires 0 <= newLength;
      @ ensures \fresh(\result) && \result.length == newLength;
      @ ensures (\forall \bigint i; 0 <= i && i < newLength;
      @ 	\result[i] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static int[] copyOf(int[] original, int newLength) {
        int[] copy = new int[newLength];
        int l = Math.min(original.length, newLength);
        /*@ loop_invariant 0 <= i <= l;
          @ loop_invariant (\forall \bigint j; 0 <= j && j < i; copy[j] == original[j]);
          @ assignable copy[0..l - 1];
          @ decreases l - i;
          @*/
        for (int i = 0; i < l; ++i) {
            copy[i] = original[i];
        }
        return copy;
    }

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
    public static float[] copyOfRange(float[] original, int from, int to) {
        //@ assert 0.0f == 0.0f;
        int newLength = to - from;
        if (newLength < 0)
            throw new IllegalArgumentException(from + " > " + to);
        float[] copy = new float[newLength];

        int l = Math.min(original.length, to);
        /*@ loop_invariant from <= i <= l;
          @ loop_invariant (\forall \bigint j; from <= j && j < i;
          @     j < original.length ?
          @         Float._isSame(copy[j - from], original[j]) :
          @         copy[j - from] == 0.0f
          @ );
          @ assignable copy[0..l - from - 1];
          @ decreases l - i;
          @*/
        for (int i = from; i < l; ++i) {
            copy[i - from] = original[i];
        }
        return copy;
    }

    /*@ public normal_behavior
      @ requires 0 <= from <= to && from <= original.length;
      @ ensures \fresh(\result) && \result.length == to - from;
      @ ensures (\forall \bigint i; from <= i && i < to;
      @ 	\result[i - from] == (i < original.length ? original[i] : 0)
      @ );
      @ assignable \nothing;
      @*/
    public static int[] copyOfRange(int[] original, int from, int to) {
        int newLength = to - from;
        if (newLength < 0)
            throw new IllegalArgumentException(from + " > " + to);
        int[] copy = new int[newLength];

        int l = Math.min(original.length, to);
        /*@ loop_invariant from <= i <= l;
          @ loop_invariant (\forall \bigint j; from <= j && j < i; copy[j - from] == original[j]);
          @ assignable copy[0..l - from - 1];
          @ decreases l - i;
          @*/
        for (int i = from; i < l; ++i) {
            copy[i - from] = original[i];
        }
        return copy;
    }
}
