// noException: true
// verbose: true

// Positive control for the JmlSideEffectChecker: none of these clauses contains a side-effecting
// construct. The checker must not over-fire on pure arithmetic, on reads of ghost variables, or
// on `set` statements (whose assignment is the point, not a forbidden side effect).

class NoSideEffects {

    //@ protected nullable ghost int ghostField = 0;

    /*@ public normal_behavior
      @  requires ghostField >= 0;
      @  ensures \result == ghostField + arg;
      @  assignable ghostField;
      @*/
    public int accumulate(int arg) {
        //@ set ghostField = ghostField + arg;
        return ghostField;
    }
}
