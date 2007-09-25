

package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
public class IdentityHashMap extends AbstractMap
  implements Map, Serializable, Cloneable {
    static final Object tombstone = new Object();
    static final Object emptyslot = new Object();
    int size;
    transient Object[] table;
    transient int modCount;
    public IdentityHashMap() {}
    public IdentityHashMap(int max) {}
    public IdentityHashMap(Map m) {}
    public void clear() {}
    public Object clone() {}
    public boolean containsKey(Object key) {}
    public boolean containsValue(Object value) {}
    public Set entrySet() {}
    public boolean equals(Object o) {}
    public Object get(Object key) {}
    public int hashCode() {}
    public boolean isEmpty() {}
    public Set keySet() {}
    public Object put(Object key, Object value) {}
    public void putAll(Map m) {}
    public Object remove(Object key) {}
    public int size() {}
    public Collection values() {}
    int hash(Object key) {}
    private final class IdentityIterator implements Iterator {
        final int type;
        int knownMod = modCount;
        int count = size;
        int loc = table.length;
        IdentityIterator(int type) {}
        public boolean hasNext() {}
        public Object next() {}
        public void remove() {}
    }
    private final class IdentityEntry implements Map.Entry {
        final int loc;
        final int knownMod = modCount;
        IdentityEntry(int loc) {}
        public boolean equals(Object o) {}
        public Object getKey() {}
        public Object getValue() {}
        public int hashCode() {}
        public Object setValue(Object value) {}
        public final String toString() {}
    }
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
    private void writeObject(ObjectOutputStream s)
     throws IOException {}
}
