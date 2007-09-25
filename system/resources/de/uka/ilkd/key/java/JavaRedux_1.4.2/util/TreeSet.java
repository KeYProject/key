


package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
public class TreeSet extends AbstractSet
  implements SortedSet, Cloneable, Serializable {
    public TreeSet() {}
    public TreeSet(Comparator comparator) {}
    public TreeSet(Collection collection) {}
    public TreeSet(SortedSet sortedSet) {}
    private TreeSet(SortedMap backingMap) {}
    public boolean add(Object obj) {}
    public boolean addAll(Collection c) {}
    public void clear() {}
    public Object clone() {}
    public Comparator comparator() {}
    public boolean contains(Object obj) {}
    public Object first() {}
    public SortedSet headSet(Object to) {}
    public boolean isEmpty() {}
    public Iterator iterator() {}
    public Object last() {}
    public boolean remove(Object obj) {}
    public int size() {}
    public SortedSet subSet(Object from, Object to) {}
    public SortedSet tailSet(Object from) {}
    private void writeObject(ObjectOutputStream s) throws IOException {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
}
