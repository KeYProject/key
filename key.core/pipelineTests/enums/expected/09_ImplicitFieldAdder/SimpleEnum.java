public final class SimpleEnum extends Enum {
    //@ static invariant A != null && B != null && C != null;
    //@ static invariant A != B;
    //@ static invariant A != C;
    //@ static invariant B != C;
    //@ static invariant (\forall SimpleEnum x; A == x || B == x || C == x);

    public static final SimpleEnum A = new SimpleEnum();

    public static final SimpleEnum B = new SimpleEnum();

    public static final SimpleEnum C = new SimpleEnum();

    private static final String[] $enumConstantNames = { "A", "B", "C" };

    private static final SimpleEnum[] values = { A, B, C };

    public static void values() {
        return values;
    }

    public static SimpleEnum valueOf(String name) {
        if ("A".equals(name))
            return A;
        if ("B".equals(name))
            return B;
        if ("C".equals(name))
            return C;
        throw new IllegalArgumentException();
    }

    public String name() {
        return $enumConstantNames[ordinal()];
    }

    public int ordinal() {
        if (this == A)
            return 0;
        if (this == B)
            return 1;
        if (this == C)
            return 2;
        return 0;
    }

    @javax.annotation.processing.Generated()
    static private boolean $classInitializationInProgress;

    @javax.annotation.processing.Generated()
    static private boolean $classErroneous;

    @javax.annotation.processing.Generated()
    static private boolean $classInitialized;

    @javax.annotation.processing.Generated()
    static private boolean $classPrepared;

    @javax.annotation.processing.Generated()
    static public model boolean $staticInv;

    @javax.annotation.processing.Generated()
    static public model boolean $staticInv_free;
}
