//! deleteTmpDir : false

class Test {

    //@ model int f(int arg);

    //@ ensures true;
    void test() {
        int x = 42;
        /*@ assert (\forall int x; f(x) > 40) \by {
               obtain int y \from_goal;
               assert f(y) == 42 \by cheat;
               auto;
               // Still too verbose on auto
        } */
    }

}
