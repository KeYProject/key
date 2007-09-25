


package java.util;
public class LinkedHashMap extends HashMap {
    transient LinkedHashEntry root;
    final boolean accessOrder;
    class LinkedHashEntry extends HashEntry {
        LinkedHashEntry pred;
        LinkedHashEntry succ;
        LinkedHashEntry(Object key, Object value) {}
        void access() {}
        Object cleanup() {}
    }
    public LinkedHashMap() {}
    public LinkedHashMap(Map m) {}
    public LinkedHashMap(int initialCapacity) {}
    public LinkedHashMap(int initialCapacity, float loadFactor) {}
    public LinkedHashMap(int initialCapacity, float loadFactor,
                       boolean accessOrder) {}
    public void clear() {}
    public boolean containsValue(Object value) {}
    public Object get(Object key) {}
    protected boolean removeEldestEntry(Map.Entry eldest) {}
    void addEntry(Object key, Object value, int idx, boolean callRemove) {}
    void putAllInternal(Map m) {}
    Iterator iterator(final int type) {}
}
