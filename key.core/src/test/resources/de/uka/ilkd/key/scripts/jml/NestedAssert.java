class NestedAssert {
    //@ ensures true;
    void test() {
        int x;
        /*@ assert x > 2 \by {
              assert x == 7 \by { assume x == 7; auto; }
              auto;
        } */
    }

}
