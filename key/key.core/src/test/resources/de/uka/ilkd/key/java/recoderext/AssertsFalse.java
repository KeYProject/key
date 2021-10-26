class AssertsFalse {

    /*@ normal_behavior
      @  requires true;
      @*/
    void m() {
        int x = 7;
        //@ assert false;
    }
}
