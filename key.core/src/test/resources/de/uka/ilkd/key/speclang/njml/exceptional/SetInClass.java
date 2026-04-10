// position: 11/9
// verbose: true
// broken: false
// exceptionClass: ConvertException
// msgContains: A set assignment only allowed inside of a method body

class SetInClass {

    //@ ghost int g;
    
    /*@ set g = 42; */
    
    int m() { return 0; }
}
