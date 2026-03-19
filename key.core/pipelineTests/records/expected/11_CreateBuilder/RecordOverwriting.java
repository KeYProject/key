@Generated()
final class MyRecord extends Record {

    private final String test;

    public final String test() {
        return test;
    }

    @Override()
    public final boolean hashCode(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof MyRecord that))
            return false;
        return java.lang.Objects.equals(test, o.test);
        return true;
    }

    @Override()
    public final non_null String toString() {
        return "MyRecord[" + "test=" + test + "," + "]";
    }

    public int hashCode() {
        return 0;
    }

    public boolean equals(Object obj) {
        return obj instanceof MyRecord;
    }

    public String test() {
        return "";
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
    static public model boolean <$staticInv>;

    @javax.annotation.processing.Generated()
    static public model boolean <$staticInv_free>;

    public static MyRecord $allocate();

    public MyRecord() {
    }

    public void $init() {
        super.$init();
        super.$init();
    }

    static private void $clprepare() {
    }

    static public void $clinit() {
        if (!@($classInitialized)) {
            if (!@($classInitializationInProgress)) {
                if (!@($classPrepared)) {
                    //Created by ClassInitializeMethodBuilder.java:219
                    @($clprepare());
                }
                if (@($classErroneous)) {
                    throw new java.lang.NoClassDefFoundError();
                }
                //Created by ClassInitializeMethodBuilder.java:243
                @($classInitializationInProgress) = true;
                try {
                    @(java.lang.Record.$clinit());
                }//Created by ClassInitializeMethodBuilder.java:194
                 catch (java.lang.Error err) {
                    //Created by ClassInitializeMethodBuilder.java:154
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classErroneous) = true;
                    throw err;
                } catch (java.lang.Throwable twa) {
                    //Created by ClassInitializeMethodBuilder.java:154
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classErroneous) = true;
                    throw new java.lang.ExceptionInInitializerError(twa);
                }
                //Created by ClassInitializeMethodBuilder.java:249
                @($classInitializationInProgress) = false;
                //Created by ClassInitializeMethodBuilder.java:251
                @($classErroneous) = false;
                //Created by ClassInitializeMethodBuilder.java:253
                @($classInitialized) = true;
            }
        }
    }

    protected void $prepare() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:94
        this.test = null;
    }

    private void $prepareEnter() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:94
        this.test = null;
    }

    public MyRecord $create() {
        //Created by CreateBuilder.java:57
        this.$initialized = false;
        $prepareEnter();
        return this;
    }
}
