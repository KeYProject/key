

package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
public class Hashtable extends Dictionary
  implements Map, Cloneable, Serializable {
    static final int KEYS = 0,
                   VALUES = 1,
                   ENTRIES = 2;
    transient HashEntry[] buckets;
    transient int modCount;
    transient int size;
    private static final class HashEntry extends AbstractMap.BasicMapEntry {
        HashEntry next;
        HashEntry(Object key, Object value) {}
        public Object setValue(Object newVal) {}
    }
    public Hashtable() {}
    public Hashtable(Map m) {}
    public Hashtable(int initialCapacity) {}
    public Hashtable(int initialCapacity, float loadFactor) {}
    public synchronized int size() {}
    public synchronized boolean isEmpty() {}
    public Enumeration keys() {}
    public Enumeration elements() {}
    public synchronized boolean contains(Object value) {}
    public boolean containsValue(Object value) {}
    public synchronized boolean containsKey(Object key) {}
    public synchronized Object get(Object key) {}
    public synchronized Object put(Object key, Object value) {}
    public synchronized Object remove(Object key) {}
    public synchronized void putAll(Map m) {}
    public synchronized void clear() {}
    public synchronized Object clone() {}
    public synchronized String toString() {}
    public Set keySet() {}
    public Collection values() {}
    public Set entrySet() {}
    public boolean equals(Object o) {}
    public synchronized int hashCode() {}
    private int hash(Object key) {}
    HashEntry getEntry(Object o) {}
    void putAllInternal(Map m) {}
    protected void rehash() {}
    private synchronized void writeObject(ObjectOutputStream s)
     throws IOException {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
    private final class HashIterator implements Iterator {
        final int type;
        int knownMod = modCount;
        int count = size;
        int idx = buckets.length;
        HashEntry last;
        HashEntry next;
        HashIterator(int type) {}
        public boolean hasNext() {}
        public Object next() {}
        public void remove() {}
    }
    private final class Enumerator implements Enumeration {
        final int type;
        int count = size;
        int idx = buckets.length;
        HashEntry next;
        Enumerator(int type) {}
        public boolean hasMoreElements() {}
        public Object nextElement() {}
    }
}
