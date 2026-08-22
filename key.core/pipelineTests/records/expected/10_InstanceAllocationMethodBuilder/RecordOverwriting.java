@javax.annotation.processing.Generated("RecordClassBuilder")
final class MyRecord extends Record {

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final String test;

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures test == this.test;
      @ assignable this.*;

      @*/
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public MyRecord(String test) {
        //Created by RecordClassBuilder.java:131
        this.test = test;
    }

    @Override()
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final non_null String toString() {
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
    static public model boolean $staticInv;

    @javax.annotation.processing.Generated()
    static public model boolean $staticInv_free;

    public static MyRecord $allocate();
}
