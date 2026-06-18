// position: 11/34
// verbose: true
// broken: false
// exceptionClass: ParserException
// msgContains: expected, but found '('

class MethodInMethod {

    int m() {

        /*@ model int modelMethod() { return 0; } */
        
        return 0;
    }
}
