class Subclass {
    final int finalField;

    //@ ensures b;
    Subclass(boolean b) {
        int before = getFinalField();
        finalField = 42;
        int after = getFinalField();
    }

    int getFinalField() {
        return 0;
    }
}

class Subsubclass extends Subclass {
    /*@ normal_behaviour
      @  ensures \result == finalField;
      @*/
    int getFinalField() {
        return finalField;
    }
}
