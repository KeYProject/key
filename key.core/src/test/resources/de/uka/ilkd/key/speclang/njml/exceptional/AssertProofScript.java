// noException: true
// verbose: true

// Positive control for JML assertion proof scripts: `assert e \by { ... }` must load and the
// script must be kept (re-parsed against KeY's own grammar in JP2KeYConverter), not dropped.

class AssertProofScript {

    int x;

    void m() {
        //@ assert x > 0 \by { auto; };
        //@ assume x <= 0;
        //@ assert x != 0;
    }
}
