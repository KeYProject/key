public class SuffixArray {

    private final int[] a;
    private final int[] suffixes;
    private final int N;

    /*@ normal_behavior
      @ ensures this.a == a;
      @ ensures N == a.length && N == suffixes.length;
      @ pure
      @*/
    public SuffixArray(int[] a) {
        this.a = a;
        N = a.length;
        suffixes = new int[N];
        for (int i = 0; i < N; i++) suffixes[i] = i;
        sort(suffixes);
    }


    /*@ normal_behavior
      @ requires 0 <= i && i < suffixes.length;
      @ ensures \result == suffixes[i];
      @ strictly_pure
      @*/
    public int select(int i) { 
        return suffixes[i]; 
    }


  /*@ normal_behavior
    @ requires 0 <= x && x < suffixes.length;
    @ requires 0 <= y && y < suffixes.length;
    @ requires x != y;
    @ ensures (\forall int i; 0 <= i && i < \result; suffixes[x+i]==suffixes[y+i]);
    @ ensures suffixes[x+\result]!=suffixes[y+\result] || \result == suffixes.length-x || \result == suffixes.length-y;
    @ strictly_pure
    @*/
 
    private int lcp(int x, int y) {
        int l = 0;
        while (x+l<N && y+l<N && a[x+l]==a[y+l]) {
            l++;
        }
        return l;
    }


    public int lcp(int i) {
        return lcp(suffixes[i], suffixes[i-1]);
    }


    public int compare(int x, int y) {
        if (x == y) return 0;
        int l = 0;

        while (x+l<N && y+l<N && a[x+l] == a[y+l]) {
            l++;
        }

        if (x+l == N) return -1;
        if (y+l == N) return 1;
        if (a[x+l] < a[y+l]) return -1;
        if (a[x+l] > a[y+l]) return 1;
        
        throw new RuntimeException();
    }


    public void sort(final int[] data) {
        for(int i = 0; i < data.length + 0; i++) {
            for(int j = i; j > 0 && compare(data[j - 1], data[j]) > 0; j--) {
                final int b = j - 1;
                final int t = data[j];
                data[j] = data[b];
                data[b] = t;
            }
        }
    }

/*
    public static void main(String[] argv) {
        int[] arr = {1,2,2,5};
        SuffixArray sa = new SuffixArray(arr);
        System.out.println(sa.lcp(1,2));
        int[] brr = {1,2,3,5};
        sa = new SuffixArray(brr);
        System.out.println(sa.lcp(1,2));
        int[] crr = {1,2,3,5};
        sa = new SuffixArray(crr);
        System.out.println(sa.lcp(2,3));
        int[] drr = {1,2,3,3};
        sa = new SuffixArray(drr);
        System.out.println(sa.lcp(2,3));
    }
*/

}



//Based on code by Robert Sedgewick and Kevin Wayne.
