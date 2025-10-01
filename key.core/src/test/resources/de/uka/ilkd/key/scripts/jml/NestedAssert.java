class Test {
    //@ ensures true;
    void test() {
        int x;
        /*@ assert x > 2 \by {
              assert x == 7 \by { cheat; }
              auto; // should not be necessary ... eventually removed
        } */
    }

}
