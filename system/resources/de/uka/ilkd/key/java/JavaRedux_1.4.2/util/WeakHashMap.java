


package java.util;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
public class WeakHashMap extends AbstractMap implements Map {
    static final Object NULL_KEY = new Object(){
        public int hashCode() {}
        public boolean equals(Object o) {}
    };
    int size;
    int modCount;
    private final class WeakEntrySet extends AbstractSet {
        WeakEntrySet() {}
        public int size() {}
        public Iterator iterator() {}
    }
    private static class WeakBucket extends WeakReference {
        Object value;
        WeakBucket next;
        int slot;
        public WeakBucket(Object key, ReferenceQueue queue, Object value,
                      int slot) {}
        class WeakEntry implements Map.Entry {
            Object key;
            public WeakEntry(Object key) {}
            public WeakBucket getBucket() {}
            public Object getKey() {}
            public Object getValue() {}
            public Object setValue(Object newVal) {}
            public int hashCode() {}
            public boolean equals(Object o) {}

            public String toString() {}
        }
        WeakEntry getEntry() {}
    }
    WeakBucket[] buckets;
    public WeakHashMap() {}
    public WeakHashMap(int initialCapacity) {}
    public WeakHashMap(int initialCapacity, float loadFactor) {}
    public WeakHashMap(Map m) {}
    private int hash(Object key) {}
    void cleanQueue() {}
    private void rehash() {}
    private WeakBucket.WeakEntry internalGet(Object key) {}
    private void internalAdd(Object key, Object value) {}
    void internalRemove(WeakBucket bucket) {}
    public int size() {}
    public boolean isEmpty() {}
    public boolean containsKey(Object key) {}
    public Object get(Object key) {}
    public Object put(Object key, Object value) {}
    public Object remove(Object key) {}
    public Set entrySet() {}
    public void clear() {}
    public boolean containsValue(Object value) {}
    public Set keySet() {}
    public void putAll(Map m) {}
    public Collection values() {}
}
