// noException: false
// exceptionClass: IllegalArgumentException
// msgContains: datagroup family
// verbose: true

// JMLtk parses class level `datagroup` clauses as JmlFieldDeclaration with the keyword as a
// bogus type; unwrapping them would silently install a spurious field. The JMLTransformer
// rejects the whole datagroup family loudly (guard, no spurious fields).

class Datagroup {

    //@ datagroup group;
    int x;
}
