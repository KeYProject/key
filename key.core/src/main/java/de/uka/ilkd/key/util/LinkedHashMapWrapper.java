/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.equality.EqualsModProperty;
import de.uka.ilkd.key.logic.equality.Property;

import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;


/**
 * This class is a wrapper for {@link LinkedHashMap} where the keys are elements that implement
 * {@link EqualsModProperty}.
 *
 * @param <K> the type of the keys in the wrapped LinkedHashMap
 * @param <V> the type of the values in the wrapped LinkedHashMap
 */
public class LinkedHashMapWrapper<K extends EqualsModProperty<K>, V> {
    /*
     * Internally, the elements are wrapped so that EqualsModProperty can be used for equality
     * checks and hash codes instead of the usual equals and hashCode methods.
     */

    /**
     * The wrapped {@link LinkedHashMap}.
     */
    private final LinkedHashMap<ElementWrapper<K>, @Nullable V> map;

    /**
     * The {@link Property<K>} that is used for equality checks and hash codes.
     */
    private final Property<K> property;

    /**
     * Constructs a new empty {@link LinkedHashMapWrapper}.
     *
     * @param property the {@link Property<Term>} that is used internally for equality checks and
     *        hash codes
     */
    public LinkedHashMapWrapper(Property<K> property) {
        this.property = property;
        map = new LinkedHashMap<>();
    }

    /**
     * Constructs a new {@link LinkedHashMapWrapper} and inserts the given key-value pair.
     *
     * @param key the key to be inserted
     * @param value the value corresponding to {@code key}
     * @param property the {@link Property<Term>} that is used internally for equality checks and
     *        hash codes
     */
    public LinkedHashMapWrapper(K key, V value, Property<K> property) {
        this(property);
        put(key, value);
    }

    /**
     * Constructs a new {@link LinkedHashMapWrapper} and inserts the given key-value pairs.
     * <p>
     * The first key in {@code keys} is mapped to the first value in {@code values} etc.
     * If there are more keys than values, the remaining keys are mapped to {@code null}.
     * If there are more values than keys, the remaining values are ignored.
     *
     * @param keys the array of keys to be inserted
     * @param values the array of values corresponding to the keys
     * @param property the {@link Property<Term>} that is used internally for equality checks and
     *        hash codes
     */
    public LinkedHashMapWrapper(K[] keys, V[] values, Property<K> property) {
        this(property);
        putAll(keys, values);
    }

    /**
     * Constructs a new {@link LinkedHashMapWrapper} and inserts the given key-value pairs.
     * <p>
     * The first key in {@code keys} is mapped to the first value in {@code values} etc.
     * If there are more keys than values, the remaining keys are mapped to {@code null}.
     * If there are more values than keys, the remaining values are ignored.
     *
     * @param keys the iterable of keys to be inserted
     * @param values the iterable of values corresponding to the keys
     * @param property the {@link Property<Term>} that is used internally for equality checks and
     *        hash codes
     */
    public LinkedHashMapWrapper(Iterable<K> keys, Iterable<V> values, Property<K> property) {
        this(property);
        putAll(keys, values);
    }

    /**
     * Returns the number of key-value pairs in this map.
     *
     * @return the number of key-value pairs in this map
     */
    public int size() {
        return map.size();
    }

    /**
     * Returns true if this map contains no key-value pairs.
     *
     * @return true if this map contains no key-value pairs
     */
    public boolean isEmpty() {
        return map.isEmpty();
    }

    /**
     * Returns true if this map contains a mapping for the specified key.
     *
     * @param key the key whose presence in this map is to be tested
     * @return true if this map contains a mapping for the specified key
     */
    public boolean containsKey(K key) {
        return map.containsKey(wrapKey(key));
    }

    /**
     * Returns the value to which the specified key is mapped, or {@code null} if this map contains
     * no mapping for the key.
     *
     * @param key the key whose associated value is to be returned
     * @return the value to which the specified key is mapped
     */
    public @Nullable V get(K key) {
        return map.get(wrapKey(key));
    }

    /**
     * Insert the given key-value pair into this map.
     * <p>
     * If the map previously contained a mapping for the key, the old value is replaced by the given
     * value.
     *
     * @param key the key to be inserted
     * @param value the value corresponding to {@code key}
     * @return the previous value associated with {@code key}, or {@code null} if there was no
     *         mapping for {@code key}
     */
    public @Nullable V put(K key, @Nullable V value) {
        return map.put(wrapKey(key), value);
    }

    /**
     * Inserts the given key-value pairs into this map.
     * <p>
     * The first key in {@code keys} is mapped to the first value in {@code values} etc.
     * If there are more keys than values, the remaining keys are mapped to {@code null}.
     * If there are more values than keys, the remaining values are ignored.
     *
     * @param keys the array of keys to be inserted
     * @param vals the array of values corresponding to the keys
     */
    public void putAll(K[] keys, V[] vals) {
        for (int i = 0; i < keys.length; i++) {
            if (i < vals.length) {
                put(keys[i], vals[i]);
            } else {
                put(keys[i], null);
            }
        }
    }

    /**
     * Inserts the given key-value pairs into this map.
     * <p>
     * The first key in {@code keys} is mapped to the first value in {@code values} etc.
     * If there are more keys than values, the remaining keys are mapped to {@code null}.
     * If there are more values than keys, the remaining values are ignored.
     *
     * @param keys the iterable of keys to be inserted
     * @param vals the iterable of values corresponding to the keys
     */
    public void putAll(Iterable<K> keys, Iterable<V> vals) {
        Iterator<V> itVals = vals.iterator();
        for (K key : keys) {
            if (itVals.hasNext()) {
                put(key, itVals.next());
            } else {
                put(key, null);
            }
        }
    }

    /**
     * Removes the mapping for the specified key from this map if present and returns the previously
     * associated value.
     *
     * @param key the key whose mapping is to be removed from the map
     * @return the previous value associated with {@code key}, or {@code null} if there was no
     *         mapping for {@code key}
     */
    public @Nullable V remove(K key) {
        return map.remove(wrapKey(key));
    }

    /**
     * Returns true if this map contains a mapping to the specified value.
     *
     * @param value the value whose presence in this map is to be tested
     * @return true if this map contains a mapping to the specified value
     */
    public boolean containsValue(V value) {
        return map.containsValue(value);
    }

    /**
     * Returns an iterator over the key-value pairs in this map.
     * <p>
     * The pairs in this iterator contain the unwrapped terms.
     *
     * @return an iterator over the key-value pairs in this map
     */
    public Iterator<Pair<K, V>> iterator() {
        return new PairIterator<>(map);
    }

    /**
     * This helper method wraps an element in an {@link ElementWrapper} with the {@link Property<K>}
     * of this map.
     * <p>
     * This is done so that {@link EqualsModProperty} can be used for equality checks and hash codes
     * instead of the usual {@code equals} and {@code hashCode} methods in the internal
     * {@link LinkedHashMap}.
     *
     * @param key the key to be wrapped
     * @return the wrapped key
     */
    private ElementWrapper<K> wrapKey(K key) {
        return new ElementWrapper<K>(key, property);
    }


    // ------------- wrapper class for keys in the internal map
    /**
     * This class is used to wrap an element and override the {@code equals} and {@code hashCode}
     * methods for use in a map.
     * <p>
     * The wrapped element is equipped with a {@link Property<K>} that is used for
     * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} and
     * {@link EqualsModProperty#hashCodeModProperty(Property)} instead of the normal
     * {@code equals} implementation.
     *
     * @param <K> the type of the wrapped element
     */
    private static class ElementWrapper<K extends EqualsModProperty<K>> {
        /**
         * The wrapped element.
         */
        K key;

        /**
         * The {@link Property<K>} that is used for equality checks and hash codes.
         */
        Property<K> property;

        /**
         * Creates a new wrapper for the given element.
         *
         * @param key the element to be wrapped
         * @param property the {@link Property<K>} that is used for equality checks and hash codes
         */
        public ElementWrapper(K key, Property<K> property) {
            this.key = key;
            this.property = property;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj instanceof ElementWrapper<?> other) {
                return key.equalsModProperty(other.key, property);
            }
            return false;
        }

        @Override
        public int hashCode() {
            return key.hashCodeModProperty(property);
        }
    }


    // ------------- class to iterate over internal map and unwrap terms
    /**
     * This class is used to iterate over the key-value pairs in the {@link LinkedHashMapWrapper}.
     * <p>
     * The keys in the pairs are unwrapped before returning them.
     *
     * @param <K> the type of the keys in the {@link LinkedHashMapWrapper}
     * @param <V> the type of the values in the {@link LinkedHashMapWrapper}
     */
    private static class PairIterator<K extends EqualsModProperty<K>, V>
            implements Iterator<Pair<K, V>> {
        /**
         * The iterator over the keys of the internal map.
         */
        private final Iterator<ElementWrapper<K>> keyIt;

        /**
         * The internal map.
         */
        private final LinkedHashMap<ElementWrapper<K>, V> map;

        /**
         * The last key-value pair that was returned by {@link #next()}.
         */
        private @Nullable ElementWrapper<K> last = null;

        /**
         * Creates a new iterator over the key-value pairs in the {@link LinkedHashMapWrapper}.
         *
         * @param map the internal map of the {@link LinkedHashMapWrapper} to iterate over
         */
        public PairIterator(final LinkedHashMap<ElementWrapper<K>, V> map) {
            this.map = map;
            keyIt = map.keySet().iterator();
        }

        @Override
        public boolean hasNext() {
            return keyIt.hasNext();
        }

        @Override
        public Pair<K, V> next() {
            last = keyIt.next();
            return new Pair<>(last.key, map.get(last));
        }

        @Override
        public void remove() {
            if (last != null) {
                map.remove(last);
                last = null;
            }
        }

    }
}
