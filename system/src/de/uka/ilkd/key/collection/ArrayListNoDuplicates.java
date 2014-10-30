package de.uka.ilkd.key.collection;

import java.util.ArrayList;
import java.util.Collection;

/**
 * List implementation similar to {@link java.util.ArrayList},
 * but without duplicates.
 * @author bruns
 */
public class ArrayListNoDuplicates<T> extends ArrayList<T> {

    private static final long serialVersionUID = 4084849502501687761L;

    public ArrayListNoDuplicates() {}
    
    public ArrayListNoDuplicates(Collection<? extends T> ts) {
        addAll(ts);
    }

    @Override
    public boolean add(T t) {
        if (contains(t)) return false;
        return super.add(t);
    }

    @Override
    public void add(int i, T t) {
        if (!contains(t)) super.add(i, t);
    }
    
    @Override
    public boolean addAll(Collection<? extends T> ts) {
        boolean result = true;
        for (T t: ts) {
            result &= add(t);
        }
        return result;
    }
    
    @Override
    public boolean addAll(int i, Collection<? extends T> ts) {
        throw new UnsupportedOperationException();
    }
}
