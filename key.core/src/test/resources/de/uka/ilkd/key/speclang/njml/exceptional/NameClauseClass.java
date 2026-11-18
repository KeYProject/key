// noException: false
// exceptionClass: ProofInputException
// msgContains: Case B
// verbose: true

// Class level `name "..."` clauses are not parsed by JMLtk; the parse problem must surface
// loudly instead of leaving a silently dropped spec.
//
// Note: named spec cases are written as `[behavior] <name>:` prefixes on method level
// (e.g. `public normal_behavior CaseA: ...`), which JMLtk parses into JmlContract.name.
// There is no JMLtk counterpart for a class level spec name, so the legacy string form
// stays a loud error at class level.

class NameClauseClass {

    //@ name "Case B";
    int x;
}
