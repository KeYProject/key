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
        return java.lang.Objects.equals(from, that.from) && java.lang.Objects.equals(to, that.to);
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
    static public model boolean $staticInv;

    @javax.annotation.processing.Generated()
    static public model boolean $staticInv_free;

    public static Mapping $allocate();
}
