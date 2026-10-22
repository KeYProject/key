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

    @javax.annotation.processing.Generated()
    static public model boolean $staticInv;

    @javax.annotation.processing.Generated()
    static public model boolean $staticInv_free;

    public static Test $allocate();

    public Test() {
    }

    private void $objectInitializer0() {
        memberVar = 42;
    }

    public void $init() {
        super.$init();
        $objectInitializer0();
        super.$init();
        $objectInitializer0();
    }

    private void $objectInitializer0() {
        memberVar = 42;
    }

    static private void $clprepare() {
    }

    static public void $clinit() {
        if (!@($classInitialized)) {
            if (!@($classInitializationInProgress)) {
                if (!@($classPrepared)) {
                    //Created by ClassInitializeMethodBuilder.java:220
                    @($clprepare());
                }
                if (@($classErroneous)) {
                    throw new java.lang.NoClassDefFoundError();
                }
                //Created by ClassInitializeMethodBuilder.java:244
                @($classInitializationInProgress) = true;
                try {
                    @(java.lang.Object.$clinit());
                    {
                        // should be resolved to 2
                        abc = 1 + 1;
                    }
                }//Created by ClassInitializeMethodBuilder.java:195
                 catch (java.lang.Error err) {
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:156
                    @($classErroneous) = true;
                    throw err;
                } catch (java.lang.Throwable twa) {
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:156
                    @($classErroneous) = true;
                    throw new java.lang.ExceptionInInitializerError(twa);
                }
                //Created by ClassInitializeMethodBuilder.java:250
                @($classInitializationInProgress) = false;
                //Created by ClassInitializeMethodBuilder.java:252
                @($classErroneous) = false;
                //Created by ClassInitializeMethodBuilder.java:254
                @($classInitialized) = true;
            }
        }
    }

    protected void $prepare() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:95
        this.memberVar = 0;
    }

    private void $prepareEnter() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:95
        this.memberVar = 0;
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

    @javax.annotation.processing.Generated()
    static public model boolean $staticInv;

    @javax.annotation.processing.Generated()
    static public model boolean $staticInv_free;

    public static SubClass $allocate();

    public SubClass() {
    }

    private void $objectInitializer0() {
        memberVar = 41;
    }

    public void $init() {
        super.$init();
        $objectInitializer0();
        super.$init();
        $objectInitializer0();
    }

    private void $objectInitializer0() {
        memberVar = 41;
    }

    static private void $clprepare() {
    }

    static public void $clinit() {
        if (!@($classInitialized)) {
            if (!@($classInitializationInProgress)) {
                if (!@($classPrepared)) {
                    //Created by ClassInitializeMethodBuilder.java:220
                    @($clprepare());
                }
                if (@($classErroneous)) {
                    throw new java.lang.NoClassDefFoundError();
                }
                //Created by ClassInitializeMethodBuilder.java:244
                @($classInitializationInProgress) = true;
                try {
                    @(Test.$clinit());
                }//Created by ClassInitializeMethodBuilder.java:195
                 catch (java.lang.Error err) {
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:156
                    @($classErroneous) = true;
                    throw err;
                } catch (java.lang.Throwable twa) {
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:156
                    @($classErroneous) = true;
                    throw new java.lang.ExceptionInInitializerError(twa);
                }
                //Created by ClassInitializeMethodBuilder.java:250
                @($classInitializationInProgress) = false;
                //Created by ClassInitializeMethodBuilder.java:252
                @($classErroneous) = false;
                //Created by ClassInitializeMethodBuilder.java:254
                @($classInitialized) = true;
            }
        }
    }

    protected void $prepare() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:95
        this.memberVar = 0;
    }

    private void $prepareEnter() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:95
        this.memberVar = 0;
    }
}
