//MSG .*operator.*+.*not compatible.*with arguments.*Object.*int.*
//LINE 11
//COL 24

class ArrayMax {

    int max;

    /*@ public normal_behaviour
      @   requires a.length > 0;
      @   ensures this + max == 0;
      @*/
    public int m(int a[]) {
        max = a[0];

        /*@ loop_invariant
          @   0<=i && i<= a.length &&
          @   (\forall int j; 0<= j && j < i; a[j] <= max) &&
          @   (i == 0 ? 
          @      max == a[0] :
          @      (\exists int j; 0<= j && j < i; a[j] == max));
          @ assignable this.max;
          @ decreases a.length - i;
          @*/
        for(int i = 0; i < a.length; i++) {
            if(max < a[i]) {
                max = a[i];
            }
        }
        return max;
    }

}

/* +-operator was used for for arguments of types Object and int, for which it is not defined. */

