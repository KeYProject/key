@Generated()
final class Mapping extends Record {

    private final String from;

    public final String from() {
        return from;
    }

    private final String to;

    public final String to() {
        return to;
    }

    @Override()
    public final boolean hashCode(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Mapping that))
            return false;
        return java.lang.Objects.equals(from, o.from) && java.lang.Objects.equals(to, o.to);
        return true;
    }

    @Override()
    public final int hashCode() {
        return java.lang.Objects.hash(from, to);
    }

    @Override()
    public final non_null String toString() {
        return "Mapping[" + "from=" + from + "," + "to=" + to + "," + "]";
    }

    Mapping {
        // compact constructor!
        from = "abc";
        to = "def";
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

    public static Mapping $allocate();

    public Mapping() {
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
        this.from = null;
        //Created by PrepareObjectBuilder.java:94
        this.to = null;
    }

    private void $prepareEnter() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:94
        this.from = null;
        //Created by PrepareObjectBuilder.java:94
        this.to = null;
    }
}
