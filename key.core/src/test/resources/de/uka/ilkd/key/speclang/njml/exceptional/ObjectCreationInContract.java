// noException: false
// exceptionClass: JmlSideEffectException
// msgContains: Object creation (new java.io.File) is not allowed in a JML specification expression
// verbose: true

// JMLtk's expression grammar accepts Java object creation inside JML specifications. `new`
// has a potential side effect (allocates) and is not expressible in KeY's JML term grammar,
// so the JmlSideEffectChecker rejects it structurally.

class ObjectCreationInContract {

    /*@ public normal_behavior
      @   ensures \result == 1 || \fresh(new java.io.File("x"));
      @*/
    public int m() { return 1; }
}
