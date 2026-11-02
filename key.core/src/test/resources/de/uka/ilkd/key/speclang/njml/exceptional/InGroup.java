// noException: false
// exceptionClass: IllegalArgumentException
// msgContains: in_group
// verbose: true

// Class level `in_group` clauses belong to the datagroup family: JMLtk parses them as a
// JmlFieldDeclaration with the keyword as a bogus type. The JMLTransformer guard rejects the
// whole family loudly (no spurious fields).

class InGroup {

    //@ in_group g;
    int x;
}
