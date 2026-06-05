@javax.annotation.processing.Generated("RecordClassBuilder")
public final class SimpleRecord extends Record {

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final nullable String name;

    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final nullable String name() {
        return name;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures name == this.name;
      @ assignable this.*;

      @*/
    SimpleRecord(String name) {
        this.name = name;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures ((this == o) || (o instanceof SimpleRecord && o == null && this.name == ((SimpleRecord) o).name) || (o instanceof SimpleRecord && o == null && (this.name == null? (this.name.equals(((SimpleRecord) o).name)) : (o.name == null))))<==>\result;
      @ ensures hashCode() == o.hashCode() ==> !\result;
      @ ensures o == null ==> !\result;
      @ assignable \strictly_nothing;

      @*/
    @Override()
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final boolean equals(java.lang.Object o);

    /*@ public  normal_behavior 
      @ ensures true;
      @ requires true;
      @ assignable \strictly_nothing;

      @*/
    @Override()
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final int hashCode();

    @Override()
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final non_null String toString() {
        return "SimpleRecord[" + "name=" + name + "]";
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures name == this.name;
      @ assignable this.*;

      @*/
    SimpleRecord(String name) {
        this.name = name;
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

    public static SimpleRecord $allocate();

    void $init(String name) {
        super.$init();
        this.name = name;
    }

    void $init(String name) {
        super.$init();
        this.name = name;
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
        this.name = null;
    }

    private void $prepareEnter() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:94
        this.name = null;
    }
}
