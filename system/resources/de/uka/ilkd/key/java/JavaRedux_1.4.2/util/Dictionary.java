


package java.util;
public abstract class Dictionary {
    public Dictionary() {}
    public abstract Enumeration elements();
    public abstract Object get(Object key);
    public abstract boolean isEmpty();
    public abstract Enumeration keys();
    public abstract Object put(Object key, Object value);
    public abstract Object remove(Object key);
    public abstract int size();
}
