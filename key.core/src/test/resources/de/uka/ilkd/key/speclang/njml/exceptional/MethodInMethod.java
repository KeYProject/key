// position: 11/34
// verbose: true
// broken: false
// exceptionClass: PosConvertException
// msgContains: mismatched input '('

class MethodInMethod {

    int m() {

        /*@ model int modelMethod() { return 0; } */
        
        return 0;
    }
}
