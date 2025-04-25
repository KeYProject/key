// msgContains: mismatched input '='
// position: 12/27
// verbose: true

// Author Kai Wallisch

class WrongEquals {

    int max;

    /*@ public normal_behaviour
      @   ensures \result = max;
      @*/
    public int m() { return 42; }
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
