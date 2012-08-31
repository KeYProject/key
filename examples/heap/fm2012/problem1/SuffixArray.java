public class SuffixArray {

    private final int[] a;
    private final int[] suffixes;
    private final int N;

    /*@ invariant (\forall int i; 0 <= i && i < N; 
      @           (\exists int j; 0 <= j && j < N; suffixes[j]==i))
      @ &&
      @ 	(\forall int i,j; 0 < i && i < N && 0 <= j &&
      @            a[suffixes[i-1]+j] == a[suffixes[i]+j] 
      @            && suffixes[i-1]+j < N-1 && suffixes[i]+j < N-1;
      @            a[suffixes[i-1]+j+1] <= a[suffixes[i]+j+1]);
      @*/

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


    public int select(int i) { 
        return suffixes[i]; 
    }


    /*@ normal_behavior
      @ requires 0 <= x && x < a.length;
      @ requires 0 <= y && y < a.length;
      @ requires x != y;
      @ ensures (\forall int i; 0 <= i && i < \result; a[x+i]==a[y+i]);
      @ ensures a[x+\result]!=a[y+\result] || \result == a.length-x || \result == a.length-y;
      @ strictly_pure
      @*/
    private int lcp(int x, int y) {
        int l = 0;
        while (x+l<N && y+l<N && a[x+l]==a[y+l]) {
            l++;
        }
        return l;
    }


    /*@ normal_behavior
      @ requires 0 < i && i < N;
      @ ensures (\forall int i; 0 <= i && i < \result; a[x+i]==a[y+i]);
      @ ensures a[suffixes[i]+\result]!=a[suffixes[i-1]+\result] || \result == a.length-suffixes[i] || \result == a.length-suffixes[i-1];
      @ strictly_pure
      @*/
    public int lcp(int i) {
        return lcp(suffixes[i], suffixes[i-1]);
    }


    private int compare(int x, int y) {
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


    private void sort(final int[] data) {
        for(int i = 0; i < data.length + 0; i++) {
            for(int j = i; j > 0 && compare(data[j - 1], data[j]) > 0; j--) {
                final int b = j - 1;
                final int t = data[j];
                data[j] = data[b];
                data[b] = t;
            }
        }
    }


}



//Based on code by Robert Sedgewick and Kevin Wayne.
