class Test {
    //@ ensures true;
    void test() {
        int x = 42;
        /*@ assert x == 42 \by {
               obtain int y = 41;
               assert x+1 == 42;
            } */
    }

}