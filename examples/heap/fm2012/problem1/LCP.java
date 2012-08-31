class LCP {


  /*@ normal_behavior
    @ requires 0 <= x && x < a.length;
    @ requires 0 <= y && y < a.length;
    @ requires x != y;
    @ ensures (\forall int i; 0 <= i && i < \result; a[x+i]==a[y+i]);
    @ ensures a[x+\result]!=a[y+\result] || \result == a.length-x || \result == a.length-y;
    @ strictly_pure
    @*/
    int lcp(int[] a, int x, int y) {
        int l = 0;
        /*@ maintaining 0 <= l && l+x <= a.length && l+y <= a.length;
          @ maintaining (\forall int i; 0 <= i && i < l; a[x+i]==a[y+i]);
          @ maintaining x!=y;
          @ decreasing a.length-l;
          @ assignable \less_than_nothing;
          @*/
        while (x+l<a.length && y+l<a.length && a[x+l]==a[y+l]) {
            l++;
        }
        return l;
    }
}
