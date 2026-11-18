// verbose: true
// broken: false
// exceptionClass: ProofInputException
// msgContains: Model method modelMethod is not allowed within methods

class MethodInMethod {

    int m() {

        /*@ model int modelMethod() { return 0; } */
        
        return 0;
    }
}
