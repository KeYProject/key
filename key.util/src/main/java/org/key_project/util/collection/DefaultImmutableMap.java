/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Iterator;

import org.key_project.util.Strings;

/**
 * This class implements {@code ImmutableMap<S,T>} and provides a persistent map.
 * It is a simple implementation like lists
 */
@SuppressWarnings("nullness")
public class DefaultImmutableMap<S, T> implements ImmutableMap<S, T> {

    /** the empty map */

    @SuppressWarnings("unchecked")
    public static <S, T> DefaultImmutableMap<S, T> nilMap() {
        return (DefaultImmutableMap<S, T>) NILMap.EMPTY_MAP;
    }

    /**
     * The map this map builds on. Lookups will also consider entries in this map if the key
     * does not match {@link #entry}.
     */
    private final DefaultImmutableMap<S, T> parent;

    /**
     * The (key, value) mapping last inserted into this map.
     */
    private final ImmutableMapEntry<S, T> entry;

    /**
     * Number of entries in the map. Equal to <code>1 + parent.size</code> if entry is not null,
     * <code>parent.size</code> otherwise.
     */
    private final int size;

    /** only for use by NILMap */
    protected DefaultImmutableMap() {
        entry = null;
        this.parent = null;
        this.size = 0;
    }


    /** creates new map with mapping entry */
    protected DefaultImmutableMap(ImmutableMapEntry<S, T> entry) {
        if (entry == null) {
            throw new RuntimeException("'null' is not allowed as entry");
        }
        this.entry = entry;
        this.parent = DefaultImmutableMap.nilMap();
        this.size = 1;
    }

    /** creates new map with mapping entry and parent map */
    protected DefaultImmutableMap(ImmutableMapEntry<S, T> entry, DefaultImmutableMap<S, T> parent) {
        if (entry == null) {
            throw new IllegalArgumentException("'null' is not allowed as entry");
        }
        this.entry = entry;
        this.parent = parent;
        this.size = parent.size + 1;
    }


    /**
     * inserts mapping {@code <key,val>} into the map (old map is not modified) if key exists old
     * entry has
     * to be removed {@code null} is not allowed for key or value.
     *
     * @param key a S to be used as key
     * @param value a T to be stored as value
     * @return a ImmutableMap including the {@code <key, value>}-pair and all other pairs of the
     *         current map
     *         with keys different from the given key
     */
    public ImmutableMap<S, T> put(S key, T value) {
        return new DefaultImmutableMap<>(new MapEntry<>(key, value), this.remove(key));
    }



    /** @return value of type T that is mapped by key of type S */
    public T get(S key) {
        DefaultImmutableMap<S, T> queue = this;
        while (!queue.isEmpty()) {
            final ImmutableMapEntry<S, T> e = queue.entry;

            final S entryKey = e.key();
            if (entryKey == key || entryKey.equals(key)) {
                return e.value();
            }

            queue = queue.parent;
        }
        return null;
    }

    /** @return number of entries as int */
    public int size() {
        return size;
    }

    /** returns true if the map is empty */
    public boolean isEmpty() {
        return false;
    }

    /** @return true iff the map includes key */
    public boolean containsKey(S key) {
        DefaultImmutableMap<S, T> queue = this;
        while (!queue.isEmpty()) {
            final ImmutableMapEntry<S, T> e = queue.entry;
            final S entryKey = e.key();
            if (entryKey == key || entryKey.equals(key)) {
                return true;
            }

            queue = queue.parent;
        }
        return false;
    }

    /** @return true iff the map includes value */
    public boolean containsValue(T value) {
        DefaultImmutableMap<S, T> queue = this;
        while (!queue.isEmpty()) {
            final ImmutableMapEntry<S, T> e = queue.entry;
            final T entryVal = e.value();
            if (entryVal == value || entryVal.equals(value)) {
                return true;
            }
            queue = queue.parent;

        }
        return false;
    }

    private DefaultImmutableMap<S, T> createMap(ImmutableMapEntry<S, T>[] stack, int counter,
            DefaultImmutableMap<S, T> p_parent) {
        DefaultImmutableMap<S, T> result = p_parent;
        for (int i = 0; i < counter; i++) {
            result = new DefaultImmutableMap<>(stack[i], result);
        }
        return result;
    }

    /**
     * removes mapping (key,...) from map
     *
     * @return the new map (the same if key is not in the map)
     */
    public DefaultImmutableMap<S, T> remove(S key) {
        DefaultImmutableMap<S, T> queue = this;
        @SuppressWarnings("unchecked")
        final ImmutableMapEntry<S, T>[] stack = new ImmutableMapEntry[size()];
        int counter = 0;
        while (!queue.isEmpty()) {
            final ImmutableMapEntry<S, T> e = queue.entry;

            final S entryKey = e.key();

            if (entryKey == key || entryKey.equals(key)) {
                return createMap(stack, counter, queue.parent);
            }


            stack[counter] = e;
            counter++;

            queue = queue.parent;
        }
        return this;
    }

    /**
     * removes all mappings (...,value) from map
     *
     * @return the new map (the same if value is not mapped)
     */
    public ImmutableMap<S, T> removeAll(T value) {
        DefaultImmutableMap<S, T> queue = this;
        @SuppressWarnings("unchecked")
        final ImmutableMapEntry<S, T>[] stack = new ImmutableMapEntry[size()];
        int counter = 0;
        while (!queue.isEmpty()) {
            final ImmutableMapEntry<S, T> e = queue.entry;

            final T entryVal = e.value();

            if (entryVal != value && !entryVal.equals(value)) {
                stack[counter] = e;
                counter++;
            }

            queue = queue.parent;

        }

        return counter < stack.length
                ? createMap(stack, counter, DefaultImmutableMap.nilMap())
                : this;
    }

    /** @return iterator for all keys */
    public Iterator<S> keyIterator() {
        return new MapKeyIterator<>(this);
    }

    /** @return iterator for all values */
    public Iterator<T> valueIterator() {
        return new MapValueIterator<>(this);
    }

    /** @return iterator for entries */
    public Iterator<ImmutableMapEntry<S, T>> iterator() {
        return new MapEntryIterator<>(this);
    }

    public String toString() {
        return Strings.formatAsList(this, "[", ",", "]");
    }

    @SuppressWarnings("unchecked")
    public boolean equals(Object o) {
        if (!(o instanceof ImmutableMap)) {
            return false;
        }
        if (o == this) {
            return true;
        }

        ImmutableMap<S, T> o1 = null;
        try {
            o1 = (ImmutableMap<S, T>) o;
            if (o1.size() != size()) {
                return false;
            }
        } catch (ClassCastException cce) {
            return false;
        }


        for (ImmutableMapEntry<S, T> e : this) {
            if (!e.value().equals(o1.get(e.key()))) {
                return false;
            }
        }

        return true;
    }

    public int hashCode() {
        int hashCode = 1;
        for (ImmutableMapEntry<S, T> stImmutableMapEntry : this) {
            hashCode += 7 * stImmutableMapEntry.hashCode();
        }
        return hashCode;
    }

    /** the empty map */
    private static class NILMap<S, T> extends DefaultImmutableMap<S, T> {

        @SuppressWarnings("rawtypes")
        static final NILMap<?, ?> EMPTY_MAP = new NILMap();

        /**
         * generated serial
         */
        private static final long serialVersionUID = 412820308341055305L;

        private NILMap() {
        }

        public ImmutableMap<S, T> put(S key, T value) {
            return new DefaultImmutableMap<>(new MapEntry<>(key, value));
        }

        public T get(S key) {
            return null;
        }

        public boolean isEmpty() {
            return true;
        }

        public boolean containsKey(S key) {
            return false;
        }

        public boolean containsValue(T val) {
            return false;
        }

        public DefaultImmutableMap<S, T> remove(S key) {
            return this;
        }

        public ImmutableMap<S, T> removeAll(T value) {
            return this;
        }

        /** @return iterator for keys */
        public Iterator<S> keyIterator() {
            return ImmutableSLList.<S>nil().iterator();
        }

        /** @return iterator for values */
        public Iterator<T> valueIterator() {
            return ImmutableSLList.<T>nil().iterator();
        }

        /** @return iterator for entries */
        public Iterator<ImmutableMapEntry<S, T>> iterator() {
            return ImmutableSLList.<ImmutableMapEntry<S, T>>nil().iterator();
        }

        public int size() {
            return 0;
        }

        public String toString() {
            return "[(,)]";
        }
    }

    /**
     * inner class for the entries
     *
     * @param key   the key
     * @param value the value
     */
        private record MapEntry<S,T>(
    S key, T value)implements ImmutableMapEntry<S,T>
    {
    /**
     *
     */
    private static final long serialVersionUID = -6785625761293313622L;

    /**
     * creates a new map entry that contains key and value
     */
    private MapEntry
    {
    }

    /**
     * @return the key stored in this entry
     */
    @Override
    public S key() {
        return key;
    }

    /**
     * @return the value stored in this entry
     */
    @Override
    public T value() {
        return value;
    }

    /**
     * @return true iff both objects have equal pairs of key and value
     */
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (!(obj instanceof ImmutableMapEntry)) {
            return false;
        }
        @SuppressWarnings("unchecked")
        final ImmutableMapEntry<S, T> cmp = (ImmutableMapEntry<S, T>) obj;
        final S cmpKey = cmp.key();
        final T cmpVal = cmp.value();
        return (key == cmpKey && value == cmpVal)
                || (key.equals(cmpKey) && value.equals(cmpVal));
    }

    public String toString() {
        return key + "->" + value;
    }
}


/** iterator for the values */
private static abstract class MapIterator<S, T> {
    // stores the entry iterator
    private DefaultImmutableMap<S, T> map;

    // creates the iterator
    MapIterator(DefaultImmutableMap<S, T> map) {
        this.map = map;
    }

    /** @return true iff there are more elements */
    public boolean hasNext() {
        return !map.isEmpty();
    }

    /** @return next value in list */
    protected final ImmutableMapEntry<S, T> nextEntry() {
        final ImmutableMapEntry<S, T> entry = map.entry;
        map = map.parent;
        return entry;
    }

    /**
     * throws an unsupported operation exception as removing elements is not allowed on
     * immutable maps
     */
    public void remove() {
        throw new UnsupportedOperationException(
            "Removing elements via an iterator" + " is not supported for immutable maps.");
    }
}


/** iterator for the values */
private static final class MapEntryIterator<S, T> extends MapIterator<S, T>
        implements Iterator<ImmutableMapEntry<S, T>> {

    MapEntryIterator(DefaultImmutableMap<S, T> map) {
        super(map);
    }

    /** @return next value in list */
    public ImmutableMapEntry<S, T> next() {
        return nextEntry();
    }
}


private static final class MapValueIterator<S, T> extends MapIterator<S, T>
        implements Iterator<T> {

    MapValueIterator(DefaultImmutableMap<S, T> map) {
        super(map);
    }

    /** @return next value in list */
    public T next() {
        return nextEntry().value();
    }
}


private static final class MapKeyIterator<S, T> extends MapIterator<S, T>
        implements Iterator<S> {

    MapKeyIterator(DefaultImmutableMap<S, T> map) {
        super(map);
    }

    /** @return next value in list */
    public S next() {
        return nextEntry().key();
    }
}

}
