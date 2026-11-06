// noException: true
// verbose: true

// Method level pragma-statements: the leftover JmlDocStmt falls back to KeY's own grammar
// (nowarn_pragma/debug_statement) and unparseable leftovers are dropped silently, unlike the
// class level (see NowarnDebug.java).

class NowarnDebugInMethod {

    int m() {
        //@ nowarn;
        //@ debug;
        return 0;
    }
}
