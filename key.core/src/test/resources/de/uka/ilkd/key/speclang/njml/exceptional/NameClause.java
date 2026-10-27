// noException: false
// exceptionClass: ProofInputException
// msgContains: Case A
// verbose: true

// JMLtk cannot parse the `name "..."` clause, so this method level spec case fails to parse.
// The failure must surface loudly (a parse problem wrapped in ProofInputException) instead of
// silently dropping the whole contract.

class NameClause {

    int x;

    /*@ public normal_behavior
      @   name "Case A";
      @   ensures \result == x;
      @*/
    public int m() { return x; }
}
