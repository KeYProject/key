


package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
public class HashMap extends AbstractMap
  implements Map, Cloneable, Serializable {

    //@ public model int initialCapacity; 

    static final int DEFAULT_CAPACITY = 11;
    static final float DEFAULT_LOAD_FACTOR = 0.75f;
    final float loadFactor;
    transient HashEntry[] buckets;
    transient int modCount;
    transient int size;
    static class HashEntry extends AbstractMap.BasicMapEntry {
        HashEntry next;
        HashEntry(Object key, Object value) {}
        void access() {}
        Object cleanup() {}
    }
    public HashMap() {}

     /*@ public normal_behavior
       @    requires m != null;
       @    assignable theMap, initialCapacity, loadFactor;
       @    ensures theMap.equals(m.theMap);
       @*/
    public HashMap(Map m) {}

    /*@ public normal_behavior
       @    assignable theMap, this.initialCapacity, this.loadFactor;
       @    ensures theMap != null && theMap.isEmpty();
       @    ensures this.initialCapacity == initialCapacity;
       @*/
    public HashMap(int initialCapacity) {}

     /*@ public normal_behavior
       @    requires initialCapacity >= 0;
       @    assignable theMap, this.initialCapacity, this.loadFactor;
       @    ensures theMap != null && theMap.isEmpty();
       @    ensures this.initialCapacity == initialCapacity
       @         && this.loadFactor == loadFactor;
       @*/ 
    public HashMap(int initialCapacity, float loadFactor) {}
    public int size() {}
    public boolean isEmpty() {}
    public Object get(Object key) {}
    public boolean containsKey(Object key) {}
    public Object put(Object key, Object value) {}
    public void putAll(Map m) {}
    public Object remove(Object key) {}
    public void clear() {}
    public boolean containsValue(Object value) {}

    /*@ also
       @   public normal_behavior
       @     assignable \nothing;
       @     ensures \result instanceof Map && \fresh(\result)
       @          && ((Map)\result).equals(this);
       @     ensures_redundantly \result != this;
       @*/ 
    public Object clone() {}
    public Set keySet() {}
    public Collection values() {}
    public Set entrySet() {}
    void addEntry(Object key, Object value, int idx, boolean callRemove) {}
    final HashEntry getEntry(Object o) {}
    final int hash(Object key) {}
    Iterator iterator(int type) {}
    void putAllInternal(Map m) {}
    private void rehash() {}
    private void writeObject(ObjectOutputStream s) throws IOException {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
    private final class HashIterator implements Iterator {
        HashIterator(int type) {}
        public boolean hasNext() {}
        public Object next() {}
        public void remove() {}
    }
}
