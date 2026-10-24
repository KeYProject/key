@javax.annotation.processing.Generated("RecordClassBuilder")
final /*@ nullable */ class MyRecord extends Record {

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final String test;

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures test == this.test;
      @ assignable this.*;

      @*/
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public MyRecord(String test) {
        //Created by RecordClassBuilder.java:132
        this.test = test;
    }

    @Override()
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final /*@ non_null */ String toString() {
        return "MyRecord[" + "test=" + test + "]";
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
    static public /*@ model */ boolean $staticInv;

    @javax.annotation.processing.Generated()
    static public /*@ model */ boolean $staticInv_free;

    public static MyRecord $allocate();

    public void $init(String test) {
        super.$init();
        //Created by RecordClassBuilder.java:132
        this.test = test;
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
                    @(java.lang.Record.$clinit());
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
        this.test = null;
    }

    private void $prepareEnter() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:95
        this.test = null;
    }

    public MyRecord $create() {
        //Created by CreateBuilder.java:58
        this.$initialized = false;
        $prepareEnter();
        return this;
    }

    public static MyRecord $createObject() {
        MyRecord __NEW__;
        //Created by CreateObjectBuilder.java:71
        __NEW__ = MyRecord.$allocate();
        __NEW__.$create()@MyRecord
        return __NEW__;
    }
}
