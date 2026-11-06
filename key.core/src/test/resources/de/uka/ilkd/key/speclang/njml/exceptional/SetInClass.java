// exceptionClass: UnsolvedSymbolException
// msgContains: Unsolved symbol : set
// verbose: true
// broken: false

class SetInClass {

    //@ ghost int g;
    
    /*@ set g = 42; */
    
    int m() { return 0; }
}
