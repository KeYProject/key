//MSG .*[Mm]issing operator.*
//LINE 20
//COL 19

class ArrayMax {

    int max;

    /*@ public normal_behaviour
      @   requires a.length > 0;
      @   ensures \result == max;
      @   ensures (\forall int i; 0<= i && i < a.length; a[i] <= \result);
      @   ensures (\exists int i; 0<= i && i < a.length; a[i] == \result);
      @   assignable this.*;
      @*/
    public int m(int a[]) {
        max = a[0];

        /*@ loop_invariant
          @   0<=i  i<= a.length &&
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

/* Currently the parser message says token "i" is unexpected (line 20 column 21).
 * Perhaps it would be appropriate to inform the user that a logical operator is expected between
 * JML expressions (missing operator or something similar). */
