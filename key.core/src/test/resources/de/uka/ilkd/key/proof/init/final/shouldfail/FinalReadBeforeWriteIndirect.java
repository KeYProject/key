class FinalReadBeforeWriteIndirect {
    final int finalField;

    //@ ensures b;
    FinalReadBeforeWriteIndirect(boolean b) {
        int before = getFinalField();
        finalField = 42;
        int after = getFinalField();
    }

    /*@ normal_behaviour
      @  ensures \result == finalField;
      @*/
    private int getFinalField() {
        return finalField;
    }
}
