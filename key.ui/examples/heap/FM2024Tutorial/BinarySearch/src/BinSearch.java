class BinSearch {

    /*@ private normal_behavior
      @   requires   (\exists int idx; 0 <= idx < a.length; a[idx] == v);
      @   requires   (\forall int x, y; 0 <= x < y < a.length; a[x] <= a[y]);
      @   ensures    0 <= \result < a.length;
      @   ensures    a[\result] == v;
      @   assignable \nothing;
      @ also
      @   private exceptional_behavior
      @   requires   !(\exists int idx; 0 <= idx < a.length; a[idx] == v);
      @   assignable \nothing;
      @   signals_only RuntimeException;
      @*/
    private int binSearch(int[] a, int v) {
        int low = 0;
        int up = a.length;

    /*@ loop_invariant 0 <= low <= up <= a.length;
      @ loop_invariant (\forall int x; 0 <= x < low; a[x] != v);
      @ loop_invariant (\forall int x; up <= x < a.length; a[x] != v);
      @ assignable \nothing;
      @ decreases up - low;
      @*/
        while (low < up) {
            int mid = low + ((up - low) / 2);
            if (v == a[mid]) {
                return mid;
            } else if (v < a[mid]) {
                up = mid;
            } else {
                low = mid + 1;
            }
        }

        throw new RuntimeException();
    }

    /*@ private normal_behavior
      @   requires    0 <= low <= up <= a.length;
      @   requires    (\forall int x, y; 0 <= x < y < a.length; a[x] <= a[y]);
      @   ensures     \result == -1 || low <= \result < up;
      @   ensures     (\exists int idx; low <= idx < up; a[idx] == v) ?
      @                \result >= low && a[\result] == v : \result == -1;
      @   assignable  \nothing;
      @   measured_by up - low;
      @*/
    private int binSearchR(int[] a, int v, int low, int up) {
        if (low < up) {
            int mid = low + ((up - low) / 2);
            if (v == a[mid]) {
                return mid;
            } else if (v < a[mid]) {
                return binSearchR(a, v, low, mid);
            } else {
                return binSearchR(a, v, mid + 1, up);
            }
        }
        return -1;
    }
}