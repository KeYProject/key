// noException: false
// exceptionClass: JmlSideEffectException
// msgContains: Assignment operator '=' is not allowed in a JML specification expression
// verbose: true

// `=` inside a JML expression (here: `ensures \result = max;`) is accepted by JMLtk, which
// produces an assignment expression. Assignments carry a potential side effect and are not
// expressible in KeY's JML term grammar, so the JmlSideEffectChecker rejects the clause
// structurally instead of letting the re-serialization fail late or (worse) silently dropping
// the clause.

// Author Kai Wallisch

class WrongEquals {

    int max;

    /*@ public normal_behaviour
      @   ensures \result = max;
      @*/
    public int m() { return 42; }
}

/*
 * In this test "=" is used instead of "==".
 * It would be better to inform the user that the assignment operator "=" is not allowed in a specification expression.
 * (see http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_12.html#SEC127)
 */
