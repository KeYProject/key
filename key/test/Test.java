class Test {
    /*@
    requires b != null && a != null;
    ensures (\forall int i;
                0 <= i < \dl_seqLen(\dl_strContent(a)) && i < \dl_seqLen(\dl_strContent(b));
                \dl_strContent(a)[i] == \dl_strContent(b)[i] )
            ? \result == (\dl_seqLen(\dl_strContent(a)) - \dl_seqLen(\dl_strContent(b)))
            : (\exists int j;     (\forall int i; 0 <= i < j; \dl_strContent(a)[i] == \dl_strContent(b)[i])
                               && \result != 0 && \result == (char)\dl_seqGet(\dl_strContent(b), j) - (char)\dl_seqGet(\dl_strContent(a),j));
    */
    public int compareTo(/*@nullable*/ String a, /*@nullable*/ String b) {
        int len1 = a.length();
        int len2 = b.length();
        int lim = len1 <= len2 ? len1 : len2;
        char v1[] = a.toCharArray();
        char v2[] = b.toCharArray();

        int k = 0;

        /*@ loop_invariant
                     0 <= k <= lim
                  && (\forall int i; 0 <= i < k; \dl_strContent(a)[i] == \dl_strContent(b)[i])
                  ;
                            //\result == \dl_strContent(a).length - \dl_strContent(b).length :
                            //(\exists j; (\forall int i; 0<=i<j; a[i] == b[i]) && \result != 0 && \result == b[j]-a[j])
         */
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


    /*
    public static int compareTo(byte[] value, byte[] other, int len1, int len2) {
        int lim = Math.min(len1, len2);
        for (int k = 0; k < lim; k++) {
            if (value[k] != other[k]) {
                return getChar(value, k) - getChar(other, k);
            }
        }
        return len1 - len2;
    }
     */
}