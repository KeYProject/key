// noException: false
// exceptionClass: ProofInputException
// msgContains: Case B
// verbose: true

// Class level `name "..."` clauses are not parsed by JMLtk; the parse problem must surface
// loudly instead of leaving a silently dropped spec.

class NameClauseClass {

    //@ name "Case B";
    int x;
}
