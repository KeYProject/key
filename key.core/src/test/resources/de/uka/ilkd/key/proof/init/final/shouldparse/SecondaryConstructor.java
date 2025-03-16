class SecondaryConstructor {
    final int finalField;

    boolean b;
    
    //@ ensures b;
    SecondaryConstructor(int v) {
        finalField = v;
    }

    //@ ensures b;
    SecondaryConstructor() {
        this(42);
        int x = finalField;
    }
}
