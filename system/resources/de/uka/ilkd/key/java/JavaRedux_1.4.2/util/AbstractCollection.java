


package java.util;

import java.lang.reflect.Array;
public abstract class AbstractCollection implements Collection {
    protected AbstractCollection() {}
    public abstract Iterator iterator();
    public abstract int size();
    public boolean add(Object o) {}
    public boolean addAll(Collection c) {}
    public void clear() {}
    public boolean contains(Object o) {}
    public boolean containsAll(Collection c) {}
    public boolean isEmpty() {}
    public boolean remove(Object o) {}
    public boolean removeAll(Collection c) {}
    boolean removeAllInternal(Collection c) {}
    public boolean retainAll(Collection c) {}
    boolean retainAllInternal(Collection c) {}
    public Object[] toArray() {}
    public Object[] toArray(Object[] a) {}
    public String toString() {}
    static final boolean equals(Object o1, Object o2) {}
    static final int hashCode(Object o) {}
}
