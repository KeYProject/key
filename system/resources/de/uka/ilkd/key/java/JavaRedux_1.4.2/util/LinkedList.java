package java.util;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.reflect.Array;
public class LinkedList extends AbstractSequentialList
  implements List, Cloneable, Serializable {
    transient Entry first;
    transient Entry last;
    transient int size = 0;
    private static final class Entry {
        Object data;
        Entry next;
        Entry previous;
        Entry(Object data) {}
    }
    Entry getEntry(int n) {}
    void removeEntry(Entry e) {}
    private void checkBoundsInclusive(int index) {}
    private void checkBoundsExclusive(int index) {}
    public LinkedList() {}
    public LinkedList(Collection c) {}
    public Object getFirst() {}
    public Object getLast() {}
    public Object removeFirst() {}
    public Object removeLast() {}
    public void addFirst(Object o) {}
    public void addLast(Object o) {}
    private void addLastEntry(Entry e) {}
    public boolean contains(Object o) {}
    public int size() {}
    public boolean add(Object o) {}
    public boolean remove(Object o) {}
    public boolean addAll(Collection c) {}
    public boolean addAll(int index, Collection c) {}
    public void clear() {}
    public Object get(int index) {}
    public Object set(int index, Object o) {}
    public void add(int index, Object o) {}
    public Object remove(int index) {}
    public int indexOf(Object o) {}
    public int lastIndexOf(Object o) {}
    public ListIterator listIterator(int index) {}
    public Object clone() {}
    public Object[] toArray() {}
    public Object[] toArray(Object[] a) {}
    private void writeObject(ObjectOutputStream s) throws IOException {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
    private final class LinkedListItr implements ListIterator {
        LinkedListItr(int index) {}
        private void checkMod() {}
        public int nextIndex() {}
        public int previousIndex() {}
        public boolean hasNext() {}
        public boolean hasPrevious() {}
        public Object next() {}
        public Object previous() {}
        public void remove() {}
        public void add(Object o) {}
        public void set(Object o) {}
    }
}
