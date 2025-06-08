class LeakThis1 {
    final int finalField;

    //@ ensures b;
    LeakThis1(boolean b) {
        int before = getFinalField(this);
        finalField = 42;
        int after = getFinalField(this);
    }

    /*@ normal_behaviour
      @  ensures \result == x.finalField;
      @*/
    private int getFinalField(LeakThis1 x) {
        return x.finalField;
    }
}
