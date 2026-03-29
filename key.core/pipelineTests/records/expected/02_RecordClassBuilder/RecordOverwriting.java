@Generated()
final class MyRecord extends Record {

    private final String test;

    public final String test() {
        return test;
    }

    @Override()
    public final boolean hashCode(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof MyRecord that))
            return false;
        return java.lang.Objects.equals(test, that.test);
        return true;
    }

    @Override()
    public final non_null String toString() {
        return "MyRecord[" + "test=" + test + "," + "]";
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
}
