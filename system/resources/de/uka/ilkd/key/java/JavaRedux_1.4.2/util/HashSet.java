


package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
public class HashSet extends AbstractSet
  implements Set, Cloneable, Serializable {
    public HashSet() {}
    public HashSet(int initialCapacity) {}
    public HashSet(int initialCapacity, float loadFactor) {}
    public HashSet(Collection c) {}
    public boolean add(Object o) {}
    public void clear() {}
    public Object clone() {}
    public boolean contains(Object o) {}
    public boolean isEmpty() {}
    public Iterator iterator() {}
    public boolean remove(Object o) {}
    public int size() {}
    HashMap init(int capacity, float load) {}
    private void writeObject(ObjectOutputStream s) throws IOException {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
}
