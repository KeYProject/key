public class Test {

    public static int abc;

    static {
        // should be resolved to 2
        abc = 1 + 1;
    }

    public int memberVar;

    {
        memberVar = 42;
    }

    @javax.annotation.processing.Generated()
    static private boolean $classInitializationInProgress;

    @javax.annotation.processing.Generated()
    static private boolean $classErroneous;

    @javax.annotation.processing.Generated()
    static private boolean $classInitialized;

    @javax.annotation.processing.Generated()
    static private boolean $classPrepared;

    private void $objectInitializer0() {
        memberVar = 42;
    }

    public void $init() {
        $objectInitializer0();
        super.$init();
    }
}

public class SubClass extends Test {

    public int memberVar;

    {
        memberVar = 41;
    }

    @javax.annotation.processing.Generated()
    static private boolean $classInitializationInProgress;

    @javax.annotation.processing.Generated()
    static private boolean $classErroneous;

    @javax.annotation.processing.Generated()
    static private boolean $classInitialized;

    @javax.annotation.processing.Generated()
    static private boolean $classPrepared;

    private void $objectInitializer0() {
        memberVar = 41;
    }

    public void $init() {
        $objectInitializer0();
        super.$init();
    }
}
