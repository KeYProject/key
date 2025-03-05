class LeakThis2 {
    final int finalField;
    LeakThis2 other;

    //@ ensures b;
    LeakThis2(boolean b) {
        leakThis();
        int before = getFinalField();
        finalField = 42;
        int after = getFinalField();
    }

    private LeakThis2 leakThis() {
        other = true ? this : this;
    }

    /*@ normal_behaviour
      @  ensures \result == finalField;
      @*/
    int getFinalField() {
        return other.finalField;
    }
}
