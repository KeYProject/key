import java.lang.String;

/**
 * This class is for proving the complicated contract for {@link java.lang.String#compareTo(java.lang.String)},
 * that is used in JavaRedux and described in the JavaDoc.
 *
 * Should be provable automatically.
 *
 * @author Wolfram Pfeifer
 */
public final class String2 {
    private char[] value;

    /*@ public normal_behavior
      @  requires \invariant_for(other);
      @  ensures (\forall int i; 0 <= i < value.length && i < other.value.length; value[i] == other.value[i]) ?
      @             \result == value.length - other.value.length :
      @             (\exists int j; (\forall int k; 0 <= k < j; value[k] == other.value[k]) && \result != 0 && \result == value[j] - other.value[j]);
      @  assignable \strictly_nothing;
      @*/
    public int compareTo(String2 other) {
        int len1 = value.length;
        int len2 = other.value.length;
        int lim = min(len1, len2);
        char[] v1 = value;
        char[] v2 = other.value;

        int k = 0;
        /*@ loop_invariant 0 <= k <= lim;
          @ loop_invariant (\forall int j; 0 <= j < k; value[j] == other.value[j]);
          @ decreases lim - k;
          @ assignable \strictly_nothing;
          @*/
        while (k < lim) {
            char c1 = v1[k];
            char c2 = v2[k];
            if (c1 != c2) {
                return c1 - c2;
            }
            k++;
        }
        return len1 - len2;
    }

    /*@ normal_behavior
      @  ensures true;
      @*/
    public void testCompare() {
        assert "ab".compareTo("ac") == -1;
        assert "ac".compareTo("ab") == 1;
        assert "abc".compareTo("ab") == 1;
        assert "ab".compareTo("ab") == 0;
    }

    /*@ normal_behavior
      @  ensures a <= b ==> \result == a;
      @  ensures a > b ==> \result == b;
      @  assignable \strictly_nothing;
      @*/
    private static int min(int a, int b) {
        return a <= b ? a : b;
    }
}
