//https://mikemybytes.com/2022/02/16/java-records-and-compact-constructors/
@Generated()
final class // package-private
Name extends Record {

    private final String name;

    public final String name() {
        return name;
    }

    @Override()
    public final boolean hashCode(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Name that))
            return false;
        return java.lang.Objects.equals(name, that.name);
        return true;
    }

    @Override()
    public final int hashCode() {
        return java.lang.Objects.hash(name);
    }

    @Override()
    public final non_null String toString() {
        return "Name[" + "name=" + name + "," + "]";
    }

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
}

@Generated()
final class Point extends Record {

    private final int x;

    public final int x() {
        return x;
    }

    private final int y;

    public final int y() {
        return y;
    }

    @Override()
    public final boolean hashCode(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Point that))
            return false;
        return java.lang.Objects.equals(x, that.x) && java.lang.Objects.equals(y, that.y);
        return true;
    }

    @Override()
    public final int hashCode() {
        return java.lang.Objects.hash(x, y);
    }

    @Override()
    public final non_null String toString() {
        return "Point[" + "x=" + x + "," + "y=" + y + "," + "]";
    }

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
}
