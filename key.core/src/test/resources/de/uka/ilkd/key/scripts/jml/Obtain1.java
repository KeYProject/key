//! deleteTmpDir : false

class Test {
    //@ ensures true;
    void test() {
        int x = 42;
        /*@ assert x == 42 \by {
               obtain int y = 41;
               assert y+1 == 42 \by auto;
               auto;
               // Still too verbose on auto
        } */
    }

}
