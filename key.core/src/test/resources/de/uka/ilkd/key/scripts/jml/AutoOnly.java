//! settings:
//!   CLASS_AXIOM_OPTIONS_KEY: CLASS_AXIOM_OFF

class Test {

    //@ model int f(int arg) { return arg + arg; }

    boolean b,c,d;

    //@ ensures true;
    void test() {

        /*@ assert b && c ==> c || d \by {
               auto only:"alpha";
               rule "close" occ:"1";
        } */
    }

}
