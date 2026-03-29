@Generated()
public final class SimpleRecord extends Record {

    private final nullable String name;

    public final nullable String name() {
        return name;
    }

    @Override()
    public final boolean hashCode(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SimpleRecord that))
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
        return "SimpleRecord[" + "name=" + name + "," + "]";
    }

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
}
