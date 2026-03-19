@Generated()
public final class SimpleRecord extends Record {

    private final /*@ nullable */ nullable String name;

    public final /*@ nullable */ nullable String name() {
        return name;
    }

    @Override()
    public final boolean hashCode(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SimpleRecord that))
            return false;
        return java.lang.Objects.equals(name, o.name);
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
}
