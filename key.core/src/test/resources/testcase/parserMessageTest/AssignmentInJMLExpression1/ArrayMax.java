//MSG .*=.*
//LINE 11
//COL 27

class ArrayMax {

    int max;

    /*@ public normal_behaviour
      @   requires a.length > 0;
      @   ensures \result = max;
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

/*
 * In this test "=" is used instead of "==" (line 11).
 * Currently the parser message says something like: "result cannot be transformed into a formula".
 * It tries to convert the term "\result" (which is of type int) into a formula.
 * It would be better to inform the user that the assignment operator "=" is not allowed in a specification expression.
 * (see http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_12.html#SEC127)
 * The reason why this happens is because the semantic analysis of the JML code starts before the syntactic
 * analysis is finished.
 */
