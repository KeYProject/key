// verbose: true
// broken: false
// exceptionClass: RuntimeException
// msgContains: JML model fields cannot be declared within a method

class ModelFieldinMethod {

    int m() {

        /*@ model int modelMethod; */
        
        return 0;
    }
}


// Minssing position information :(
