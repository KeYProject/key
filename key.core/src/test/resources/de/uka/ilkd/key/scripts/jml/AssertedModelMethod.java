//! settings:
//!   CLASS_AXIOM_OPTIONS_KEY: CLASS_AXIOM_OFF

// Was a bug:
// Instantiation Test::pred(heap,self,int::select(heap,self,Test::$f)) of cutFormula (formula) does not satisfy the variable conditions

class Test {

    //@ model boolean pred(int x) { return x > 20; }

    int f;

    //@ requires pred(f);
    //@ ensures f > 2;
    void test() {
        int x;
        /*@ assert f > 2 \by {
              assert pred(f) \by { auto classAxioms:true; }
              auto; // should not be necessary ... eventually removed
        } */
    }

}
