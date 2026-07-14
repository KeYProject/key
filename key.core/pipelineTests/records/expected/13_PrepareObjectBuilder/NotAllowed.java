//https://mikemybytes.com/2022/02/16/java-records-and-compact-constructors/
@javax.annotation.processing.Generated("RecordClassBuilder")
final class // package-private
Name extends Record {

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final String name;

    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final String name() {
        return name;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures name == this.name;
      @ assignable this.*;

      @*/
    //              was package)'
    private Name(String name) {
        this.name = name;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures ((this == o) || (o instanceof Name && o == null && this.name == ((Name) o).name) || (o instanceof Name && o == null && (this.name == null? (this.name.equals(((Name) o).name)) : (o.name == null))))<==>\result;
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
        return "Name[" + "name=" + name + "]";
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures name == this.name;
      @ assignable this.*;

      @*/
    //              was package)'
    private Name(String name) {
        this.name = name;
    }

    static Name of(String name) {
        return new Name(name);
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

    public static // package-private
    Name $allocate();

    private void $init(String name) {
        super.$init();
        this.name = name;
    }

    private void $init(String name) {
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

@javax.annotation.processing.Generated("RecordClassBuilder")
final class Point extends Record {

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

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures x == this.x && y == this.y;
      @ assignable this.*;

      @*/
    Point(int x, int y) {
        // boring!
        this.x = x;
        this.y = y;
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures ((this == o) || (o instanceof Point && o == null && this.x == ((Point) o).x && this.y == ((Point) o).y) || (o instanceof Point && o == null && (x == ((Point) o).x) && (y == ((Point) o).y)))<==>\result;
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
        return "Point[" + "x=" + x + "," + "y=" + y + "]";
    }

    /*@ public  normal_behavior 
      @ requires true;
      @ ensures x == this.x && y == this.y;
      @ assignable this.*;

      @*/
    Point(int x, int y) {
        // boring!
        this.x = x;
        this.y = y;
    }

    Point(int x) {
        // a bit weird...
        // ... but perfectly fine for the compiler
        this(x, 0);
    }

    Point() {
        // fails with: 'constructor is not canonical, so its first
        //              statement must invoke another constructor'
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

    public static Point $allocate();

    void $init(int x, int y) {
        super.$init();
        // boring!
        this.x = x;
        this.y = y;
    }

    void $init(int x, int y) {
        super.$init();
        // boring!
        this.x = x;
        this.y = y;
    }

    void $init(int x) {
        this.$init(x, 0);
    }

    void $init() {
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
        this.x = 0;
        //Created by PrepareObjectBuilder.java:94
        this.y = 0;
    }

    private void $prepareEnter() {
        super.$prepare();
        //Created by PrepareObjectBuilder.java:94
        this.x = 0;
        //Created by PrepareObjectBuilder.java:94
        this.y = 0;
    }
}
