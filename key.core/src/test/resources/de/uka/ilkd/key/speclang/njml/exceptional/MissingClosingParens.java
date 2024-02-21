// verbose: true
// msgContains: missing closing parenthesis
// position: 6/40

class MissingClosingParens {
    //@ ensures (\forall int x; x > 5; x > 0 ;
    void m() { }
}

// Gives strange: no viable alternative at input '(\forall int x; x > 5; x > 0 ;'
