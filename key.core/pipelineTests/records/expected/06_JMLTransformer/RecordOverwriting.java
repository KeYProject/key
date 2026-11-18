@javax.annotation.processing.Generated("RecordClassBuilder")
/*@ nullable */ final class MyRecord extends Record {

    @javax.annotation.processing.Generated("RecordClassBuilder")
    private final String test;

    @javax.annotation.processing.Generated("RecordClassBuilder")
    public MyRecord(String test) {
        //Created by RecordClassBuilder.java:110
        this.test = test;
    }

    @Override()
    @javax.annotation.processing.Generated("RecordClassBuilder")
    public final /*@ non_null */ String toString() {
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
}
