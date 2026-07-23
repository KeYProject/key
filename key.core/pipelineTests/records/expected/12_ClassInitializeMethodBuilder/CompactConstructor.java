@javax.annotation.processing.Generated("RecordClassBuilder")
final class Mapping extends Record {

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final String from;

    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final String from() {
        return from;
    }

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final String to;

    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final String to() {
        return to;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures from == this.from && to == this.to;
      @ assignable this.*;

      @*/
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public Mapping(String from, String to) {
        {
            // compact constructor!
            from = "abc";
            to = "def";
        }
        //Created by RecordClassBuilder.java:131
        this.from = from;
        //Created by RecordClassBuilder.java:131
        this.to = to;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures ((this == o) || (o instanceof Mapping && o == null && this.from == ((Mapping) o).from && this.to == ((Mapping) o).to) || (o instanceof Mapping && o == null && (this.from == null? (this.from.equals(((Mapping) o).from)) : (o.from == null)) && (this.to == null? (this.to.equals(((Mapping) o).to)) : (o.to == null))))<==>\result;
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
        return "Mapping[" + "from=" + from + "," + "to=" + to + "]";
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

    public static Mapping $allocate();

    public void $init(String from, String to) {
        super.$init();
        {
            // compact constructor!
            from = "abc";
            to = "def";
        }
        //Created by RecordClassBuilder.java:131
        this.from = from;
        //Created by RecordClassBuilder.java:131
        this.to = to;
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
}
