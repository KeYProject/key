/*!
shouldClose: false
*/

class AutoOnly2 {

    //@ model int f(int arg) { return arg + arg; }

    boolean b,c,d;

    //@ ensures true;
    void test() {

        /*@ assert b && c ==> c || d \by {
               auto only:"beta";
        } */
    }

}
