@javax.annotation.processing.Generated("RecordClassBuilder")
final class Point3d extends Record {

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final int x;

    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final int x() {
        return x;
    }

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final int y;

    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final int y() {
        return y;
    }

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final int z;

    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final int z() {
        return z;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures x == this.x && y == this.y && z == this.z;
      @ assignable this.*;

      @*/
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public Point3d(int x, int y, int z) {
        //Created by RecordClassBuilder.java:131
        this.x = x;
        //Created by RecordClassBuilder.java:131
        this.y = y;
        //Created by RecordClassBuilder.java:131
        this.z = z;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures ((this == o) || (o instanceof Point3d && o == null && this.x == ((Point3d) o).x && this.y == ((Point3d) o).y && this.z == ((Point3d) o).z) || (o instanceof Point3d && o == null && (x == ((Point3d) o).x) && (y == ((Point3d) o).y) && (z == ((Point3d) o).z)))<==>\result;
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
        return "Point3d[" + "x=" + x + "," + "y=" + y + "," + "z=" + z + "]";
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

    public static Point3d $allocate();

    public void $init(int x, int y, int z) {
        super.$init();
        //Created by RecordClassBuilder.java:131
        this.x = x;
        //Created by RecordClassBuilder.java:131
        this.y = y;
        //Created by RecordClassBuilder.java:131
        this.z = z;
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
        this.x = 0;
        //Created by PrepareObjectBuilder.java:94
        this.y = 0;
        //Created by PrepareObjectBuilder.java:94
        this.z = 0;
    }

    private void $prepareEnter() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:94
        this.x = 0;
        //Created by PrepareObjectBuilder.java:94
        this.y = 0;
        //Created by PrepareObjectBuilder.java:94
        this.z = 0;
    }

    public Point3d $create() {
        //Created by CreateBuilder.java:57
        this.$initialized = false;
        $prepareEnter();
        return this;
    }
}
