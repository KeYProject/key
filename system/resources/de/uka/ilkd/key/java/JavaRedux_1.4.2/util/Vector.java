


package java.util;
import java.io.Serializable;
import java.lang.reflect.Array;
public class Vector extends AbstractList
  implements List, RandomAccess, Cloneable, Serializable {
    protected Object[] elementData;
    protected int elementCount;
    protected int capacityIncrement;
    public Vector() {}
    public Vector(Collection c) {}
    public Vector(int initialCapacity, int capacityIncrement) {}
    public Vector(int initialCapacity) {}
    public synchronized void copyInto(Object[] a) {}
    public synchronized void trimToSize() {}
    public synchronized void ensureCapacity(int minCapacity) {}
    public synchronized void setSize(int newSize) {}
    public synchronized int capacity() {}
    public synchronized int size() {}
    public synchronized boolean isEmpty() {}
    public Enumeration elements() {}
    public boolean contains(Object elem) {}
    public int indexOf(Object elem) {}
    public synchronized int indexOf(Object e, int index) {}
    public int lastIndexOf(Object elem) {}
    public synchronized int lastIndexOf(Object e, int index) {}
    public synchronized Object elementAt(int index) {}
    public synchronized Object firstElement() {}
    public synchronized Object lastElement() {}
    public void setElementAt(Object obj, int index) {}
    public void removeElementAt(int index) {}
    public synchronized void insertElementAt(Object obj, int index) {}
    public synchronized void addElement(Object obj) {}
    public synchronized boolean removeElement(Object obj) {}
    public synchronized void removeAllElements() {}
    public synchronized Object clone() {}
    public synchronized Object[] toArray() {}
    public synchronized Object[] toArray(Object[] a) {}
    public Object get(int index) {}
    public synchronized Object set(int index, Object element) {}
    public boolean add(Object o) {}
    public boolean remove(Object o) {}
    public void add(int index, Object element) {}
    public synchronized Object remove(int index) {}
    public void clear() {}
    public synchronized boolean containsAll(Collection c) {}
    public synchronized boolean addAll(Collection c) {}
    public synchronized boolean removeAll(Collection c) {}
    public synchronized boolean retainAll(Collection c) {}
    public synchronized boolean addAll(int index, Collection c) {}
    public synchronized boolean equals(Object o) {}
    public synchronized int hashCode() {}
    public synchronized String toString() {}
    public synchronized List subList(int fromIndex, int toIndex) {}
    protected void removeRange(int fromIndex, int toIndex) {}
    private void checkBoundInclusive(int index) {}
    private void checkBoundExclusive(int index) {}
}
