package MapCaseStudy;

public final class MapEntry {

    public final Object key;
    public Object value;

    public /*strictly_pure*/ MapEntry(Object key, Object value) {
        this.key = key;
        this.value = value;
    }

}
