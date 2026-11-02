// noException: false
// exceptionClass: IllegalArgumentException
// msgContains: maps_into
// verbose: true

// Class level `maps_into` clauses belong to the datagroup family: JMLtk parses them as a
// JmlFieldDeclaration with the keyword as a bogus type. The JMLTransformer guard rejects the
// whole family loudly (no spurious fields).

class MapsInto {

    //@ maps_into g;
    int x;
}
