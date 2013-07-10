public final class SuffixArray {

    final int[] a;
    final int[] suffixes;
    final int N;
    final LCP lcp;

    /*@ invariant (\forall int i; 0 <= i && i < N; 
      @           (\exists int j; 0 <= j && j < N; suffixes[j]==i))
      @           // suffixes is a permutation on idices
      @ &&
      @         (\forall int i; 0 <= i && i < N;
      @                  0 <= suffixes[i] && suffixes[i] < N)
      @           // follows from above, cannot hurt
      @ &&
      @         (\forall int i; 0 < i && i < N; suffixes[i-1] != suffixes[i])
      @           // follows from above, cannot hurt
      @ &&
      @ 	(\forall int i,j; 0 < i && i < N && 0 <= j &&
      @            a[suffixes[i-1]+j] == a[suffixes[i]+j] 
      @            && suffixes[i-1]+j < N-1 && suffixes[i]+j < N-1;
      @            a[suffixes[i-1]+j+1] <= a[suffixes[i]+j+1])
      @           // suffixes is ordered lexicographically
      @ && 
      @          a.length == N && suffixes.length == N;
      @*/

    /*@ normal_behavior
      @ ensures this.a == a;
      @ pure
      @*/
    public SuffixArray(int[] a) {
        this.a = a;
        N = a.length;
        suffixes = new int[N];
        for (int i = 0; i < N; i++) suffixes[i] = i;
        sort(suffixes);
        lcp = new LCP();
    }

// TODO: better spec with sortedness of suffixes in mind

    /*@ normal_behavior
      @ requires 0 < i && i < N;
      @ ensures (\forall int j; 0 <= j && j < \result; a[suffixes[i]+j]==a[suffixes[i-1]+j]);
      @ ensures a[suffixes[i]+\result]!=a[suffixes[i-1]+\result] || \result == a.length-suffixes[i] || \result == a.length-suffixes[i-1];
      @ strictly_pure helper
      @*/
    public int lcp(int i) {
        return lcp.lcp(a,suffixes[i], suffixes[i-1]);
    }


    private int compare(int x, int y) {
        if (x == y) return 0;
        int l = lcp.lcp(a,x,y);

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
