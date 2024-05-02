// verbose: true
// broken: true
// noException: false
// msgContains: outside
// exceptionClass: NotAnAssertion

// currently does not raise an exception ... but it should!

//@ invariant true;

class Outside {
    int x;

    //@ ensures true;
    void m() {}
}

//@ invariant x==2;
