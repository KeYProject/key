package MapCaseStudy;

final class MapEntry {

    public final Object key;
    public Object value;

    public /*strictly_pure*/ MapEntry(Object key, Object value) {
        this.key = key;
        this.value = value;
    }

    /*@ public normal_behaviour
     @   ensures \result == ( key == mapEntry.key && value == mapEntry.value );
     @*/
    public /*strictly_pure*/ boolean equals(MapEntry mapEntry) {
        return key == mapEntry.key && value == mapEntry.value;
    }

}
