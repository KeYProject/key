//! shouldClose: false

class Test {

    //@ model int f(int arg) { return arg + arg; }

    boolean b,c,d;

    //@ ensures true;
    void test() {

        /*@ assert b && c ==> c || d \by {
               auto only:"beta";
               rule "close";
        } */
    }

}
