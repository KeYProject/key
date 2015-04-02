package org.key_project.util.collection;

import java.util.Iterator;

/**
 * cheap implementation for an iterator over a singleton. 
 * The value {@code null} is not allowed
 */
public class SingletonIterator<T> implements Iterator<T> {

    private T element;
    
    public SingletonIterator(T element) {
        if (element == null) {
            throw new IllegalArgumentException("'null' is not allows as value for a singleton iterator.");
        }
        this.element = element;
    }
    
    @Override
    public void remove() {}
    
    @Override
    public boolean hasNext() {
        return element != null;
    }

    @Override
    public T next() {
        final T result = element;
        element = null;
        return result;
    }

}
