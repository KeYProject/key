// noException: false
// exceptionClass: IllegalArgumentException
// msgContains: readable_if
// verbose: true

// Class level `readable_if` clauses belong to the datagroup family: JMLtk parses them as a
// JmlFieldDeclaration with the keyword as a bogus type. The JMLTransformer guard rejects the
// whole family loudly (no spurious fields).

class ReadableIf {

    //@ readable_if g;
    int x;
}
