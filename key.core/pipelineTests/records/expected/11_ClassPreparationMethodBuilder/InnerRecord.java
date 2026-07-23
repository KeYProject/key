import java.lang.Object;

public class OuterClass {

    @javax.annotation.processing.Generated("RecordClassBuilder")
    final class MyRecord extends Record {

        @javax.annotation.processing.Generated("RecordClassBuilder")
        private final String test;

        @javax.annotation.processing.Generated("RecordClassBuilder")
        public final String test() {
            return test;
        }

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

        /*@ public  normal_behavior 
          @ requires true;
          @ ensures ((this == o) || (o instanceof MyRecord && o == null && this.test == ((MyRecord) o).test) || (o instanceof MyRecord && o == null && (this.test == null? (this.test.equals(((MyRecord) o).test)) : (o.test == null))))<==>\result;
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
            return "MyRecord[" + "test=" + test + "]";
        }

        @javax.annotation.processing.Generated()
        static private boolean $classInitializationInProgress;

        @javax.annotation.processing.Generated()
        static private boolean $classErroneous;

        @javax.annotation.processing.Generated()
        static private boolean $classInitialized;

        @javax.annotation.processing.Generated()
        static private boolean $classPrepared;

        private OuterClass $enclosingThis;

        @javax.annotation.processing.Generated()
        static public model boolean $staticInv;

        @javax.annotation.processing.Generated()
        static public model boolean $staticInv_free;

        public static MyRecord $allocate();

        public void $init(String test, OuterClass $ENCLOSING_THIS) {
            super.$init();
            this.$enclosingThis = $ENCLOSING_THIS;
            //Created by RecordClassBuilder.java:131
            this.test = test;
        }

        static private void $clprepare() {
        }
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

    public static OuterClass $allocate();

    public OuterClass() {
    }

    public void $init() {
        super.$init();
        super.$init();
    }

    static private void $clprepare() {
    }
}
