// verbose: true
// broken: true
// xxxexceptionClass: PosConvertException
// xxxmsgContains: XXXX

class MissingClosingParens {
    //@ ensures (\forall int x; x > 5; x > 0 ;
    void m() { }
}
