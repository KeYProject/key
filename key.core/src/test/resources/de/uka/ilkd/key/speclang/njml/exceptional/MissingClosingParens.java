// verbose: true
// msgContains: missing closing parenthesis
// position: 7/40
// broken: true

class MissingClosingParens {
    //@ ensures (\forall int x; x > 5; x > 0 ;
    void m() { }
}

// Gives strange: no viable alternative at input '(\forall int x; x > 5; x > 0 ;'
