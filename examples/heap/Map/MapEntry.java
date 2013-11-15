package MapCaseStudy;

final class MapEntry{

    public final Object key;
    public Object value;

    public /*strictly_pure*/ MapEntry(Object key, Object value) {
        this.key = key;
        this.value = value;
    }

    /*@ public normal_behaviour
     @   ensures \result == ( this.getKey() == mapEntry.getKey()
     @                     && this.getValue() == mapEntry.getValue() );
     @*/
    public /*strictly_pure*/ boolean equals(MapEntry mapEntry) {
        return this.key == mapEntry.key && this.value == mapEntry.value;
    }

}
