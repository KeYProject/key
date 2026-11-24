// noException: false
// exceptionClass: ProofInputException
// msgContains: Encountered unexpected token
// verbose: true

// JML pragma-statements `nowarn` and `debug` are absent from JMLtk's grammar. At class level the
// unparseable comment surfaces loudly as a ProofInputException instead of being silently dropped
// (status quo pinned; cf. JMLTK_GAPS.md §13).

class NowarnDebug {

    //@ nowarn;
    int x;

    //@ debug;
    int y;
}
