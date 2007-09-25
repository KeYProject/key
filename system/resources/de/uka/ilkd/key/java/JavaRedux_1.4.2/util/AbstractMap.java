


package java.util;
public abstract class AbstractMap implements Map {
    static final int KEYS = 0,
                   VALUES = 1,
                   ENTRIES = 2;
    Set keys;
    Collection values;
    protected AbstractMap() {}
    public abstract Set entrySet();
    public void clear() {}
    protected Object clone() throws CloneNotSupportedException {}
    public boolean containsKey(Object key) {}
    public boolean containsValue(Object value) {}
    public boolean equals(Object o) {}
    public Object get(Object key) {}
    public int hashCode() {}
    public boolean isEmpty() {}
    public Set keySet() {}
    public Object put(Object key, Object value) {}
    public void putAll(Map m) {}
    public Object remove(Object key) {}
    public int size() {}
    public String toString() {}
    public Collection values() {}
    static final boolean equals(Object o1, Object o2) {}
    static final int hashCode(Object o) {}
    static class BasicMapEntry implements Map.Entry {
        Object key;
        Object value;
        BasicMapEntry(Object newKey, Object newValue) {}
        public final boolean equals(Object o) {}
        public final Object getKey() {}
        public final Object getValue() {}
        public final int hashCode() {}
        public Object setValue(Object newVal) {}
        public final String toString() {}
    }
}
