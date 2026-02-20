//! settings:
//!   CLASS_AXIOM_OPTIONS_KEY: CLASS_AXIOM_OFF

class Test {

    //@ model int f(int arg) { return arg + arg; }

    int field;

    //@ ensures true;
    void test() {

        field = 21;
        int local = 42;

        /*@ assert f(field) == local \by {
               expand on: f(field);
               auto;
               // Still too verbose on auto
        } */
    }

}
