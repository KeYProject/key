// noException: false
// exceptionClass: JmlSideEffectException
// msgContains: Increment/decrement operator '++' is not allowed in a JML specification expression
// verbose: true

// JMLtk's expression grammar accepts Java's increment operators inside JML specifications.
// Increments have a potential side effect and are not expressible in KeY's JML term grammar,
// so the JmlSideEffectChecker rejects them structurally.

class IncrementInContract {

    int x;

    /*@ public normal_behavior
      @   ensures (x++) > 0;
      @*/
    public int m() { return x; }
}
