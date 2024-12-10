class SecondaryConstructor {
    final int finalField;

    boolean b;
    
    //@ ensures b;
    SecondaryConstructor(int v) {
        finalField = v;
    }

    SecondaryCosntructor() {
        this(42);
        int x = finalField;
    }
}
