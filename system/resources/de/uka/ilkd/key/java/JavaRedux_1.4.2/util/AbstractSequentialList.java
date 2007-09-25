


package java.util;
public abstract class AbstractSequentialList extends AbstractList {
    protected AbstractSequentialList() {}
    public abstract ListIterator listIterator(int index);
    public void add(int index, Object o) {}
    public boolean addAll(int index, Collection c) {}
    public Object get(int index) {}
    public Iterator iterator() {}
    public Object remove(int index) {}
    public Object set(int index, Object o) {}
}
