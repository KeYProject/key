class BinarySearch {
    /*@ public normal_behaviour
      @   requires \invariant_for(cmp);
      @   requires (\forall int x;0 <= x < a.length; a[x] != null);
      @   requires (\forall int x;
      @     (\forall int y; 0 <= x && x < y && y < a.length;
      @       cmp.compare(a[x], a[y]) <= 0));
      @   ensures \result > 0 ==> (\exists int x; 0 <= x && x < a.length; cmp.compare(a[x], v) == 0);
      // @   ensures ((\exists int x; 0 <= x && x < a.length; cmp.compare(a[x], v) == 0)
      // @       ? cmp.compare(a[\result], v) == 0
      // @       : \result == -1);

      @*/
    static /*@pure@*/ int search(Object[] a, Object v, Comparator cmp) {
        int l = 0;
        int r = a.length - 1;

        if(a.length == 0) return -1;
        if(a.length == 1) return cmp.compare(a[0], v) == 0 ? 0 : -1;

        /*@ loop_invariant 0 <= l && l < r && r < a.length
          @                && (\forall int x; 0 <= x && x < l; cmp.compare(a[x], v) < 0)
          @                && (\forall int x; r < x && x < a.length; cmp.compare(a[x], v) > 0)
	  @                && (\forall int x; 0 <= x < a.length; a[x] != null)
	  @                && \invariant_for(cmp);
          @ assignable \nothing;
          @ decreases r - l;
          @*/
        while(r > l + 1) {
            int mid = l + (r - l) / 2;

	    //@ assert 0 <= mid < a.length;

	    int c = cmp.compare(a[mid], v);
            if(c == 0) {
                return mid;
            } else if(c > 0) {
                r = mid;
            } else {
                l = mid;
            }
        }

        if(cmp.compare(a[l], v) == 0) return l;
        if(cmp.compare(a[r], v) == 0) return r;
        return -1;
    }
}


interface Comparator {
    /*@ public normal_behaviour
      @ requires true;
      @ ensures a == b ==> \result == 0;
      @ ensures \result == compare(a,b);
      @ ensures compare(a,b) < 0 <==> compare(b,a) > 0;
      @ ensures (\forall Object a,b,c; compare(a,b) == 0 && compare(b,c) == 0; compare(a,c) == 0);
      @ ensures (\forall Object a,b,c; compare(a , b) < 0 && compare(b , c) < 0; compare(a, c) < 0);
      @ ensures (\forall Object a,b,c; compare(a , b) > 0 && compare(b , c) > 0; compare(a, c) > 0);
      @ assignable \strictly_nothing;
      @*/
    int /*@ strictly_pure */ compare(Object a, Object b);
}
