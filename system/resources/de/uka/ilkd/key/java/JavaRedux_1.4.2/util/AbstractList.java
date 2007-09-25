


package java.util;
public abstract class AbstractList extends AbstractCollection implements List {
    protected transient int modCount;
    protected AbstractList() {}
    public abstract Object get(int index);
    public void add(int index, Object o) {}
    public boolean add(Object o) {}
    public boolean addAll(int index, Collection c) {}
    public void clear() {}
    public boolean equals(Object o) {}
    public int hashCode() {}
    public int indexOf(Object o) {}
    public Iterator iterator() {}
    public int lastIndexOf(Object o) {}
    public ListIterator listIterator() {}
    public ListIterator listIterator(final int index) {}
    public Object remove(int index) {}
    protected void removeRange(int fromIndex, int toIndex) {}
    public Object set(int index, Object o) {}
    public List subList(int fromIndex, int toIndex) {}
}
class SubList extends AbstractList {
    final AbstractList backingList;
    final int offset;
    int size;
    SubList(AbstractList backing, int fromIndex, int toIndex) {}
    void checkMod() {}
    private void checkBoundsInclusive(int index) {}
    private void checkBoundsExclusive(int index) {}
    public int size() {}
    public Object set(int index, Object o) {}
    public Object get(int index) {}
    public void add(int index, Object o) {}
    public Object remove(int index) {}
    protected void removeRange(int fromIndex, int toIndex) {}
    public boolean addAll(int index, Collection c) {}
    public boolean addAll(Collection c) {}
    public Iterator iterator() {}
    public ListIterator listIterator(final int index) {}
}
final class RandomAccessSubList extends SubList
  implements RandomAccess {
    RandomAccessSubList(AbstractList backing, int fromIndex, int toIndex) {}
}
