//MSG .*opening.*parenthesis.*not.*found.*
//LINE 10
//COL 32

class ArrayMax {

    int max;

    /*@ public normal_behaviour
      @   requires a.length > 0);
      @   ensures \result == max;
      @   ensures (\forall int i; 0<= i && i < a.length; a[i] <= \result);
      @   ensures (\exists int i; 0<= i && i < a.length; a[i] == \result);
      @   assignable this.*;
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


        /* @ loop_invariant
          @   0<=i && i<= a.length &&
          @   (\forall int j; 0<= j && j < i; a[j] <= max) &&
          @   (i == 0 ? max == a[0] ||
          @      (\exists int j; 0<= j && j < i; a[j] == max));
          @ assignable this.max;
          @ decreases a.length - i;
          @*/
