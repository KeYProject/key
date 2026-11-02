// noException: false
// exceptionClass: IllegalArgumentException
// msgContains: writable_if
// verbose: true

// Class level `writable_if` clauses belong to the datagroup family: JMLtk parses them as a
// JmlFieldDeclaration with the keyword as a bogus type. The JMLTransformer guard rejects the
// whole family loudly (no spurious fields).

class WritableIf {

    //@ writable_if g;
    int x;
}
