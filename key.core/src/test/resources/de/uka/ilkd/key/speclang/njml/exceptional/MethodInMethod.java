// verbose: true
// broken: false
// exceptionClass: ProofInputException
// msgContains: Encountered unexpected token

class MethodInMethod {

    int m() {

        /*@ model int modelMethod() { return 0; } */
        
        return 0;
    }
}
