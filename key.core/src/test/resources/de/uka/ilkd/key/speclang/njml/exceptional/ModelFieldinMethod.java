// verbose: true
// broken: false
// exceptionClass: ProofInputException
// msgContains: Model field modelMethod is not allowed within methods

class ModelFieldinMethod {

    int m() {

        /*@ model int modelMethod; */
        
        return 0;
    }
}

