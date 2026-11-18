// noException: false
// exceptionClass: IllegalArgumentException
// msgContains: monitors_for
// verbose: true

// Class level `monitors_for` clauses belong to the datagroup family: JMLtk parses them as a
// JmlFieldDeclaration with the keyword as a bogus type. The JMLTransformer guard rejects the
// whole family loudly (no spurious fields).

class MonitorsFor {

    //@ monitors_for g;
    int x;
}
