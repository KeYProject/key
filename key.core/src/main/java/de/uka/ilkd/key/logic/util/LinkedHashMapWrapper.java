/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.util;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.equality.EqualsModProperty;
import de.uka.ilkd.key.logic.equality.Property;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * This class is a wrapper for {@link LinkedHashMap} where the keys are {@link Term}s.
 * <p>
 * Internally, the {@link Term}s are wrapped so that {@link EqualsModProperty} can be used for
 * equality checks and
 * hash codes instead of the usual {@code equals} and {@code hashCode} methods of {@link Term}.
 *
 * @param <V> the type of the values in the wrapped LinkedHashMap
 */
public class LinkedHashMapWrapper<V> {
    /**
     * The wrapped {@link LinkedHashMap}.
     */
    private final LinkedHashMap<TermWrapper, V> map;

    /**
     * The {@link Property<Term>} that is used for equality checks and hash codes.
     */
    private final Property<Term> property;

    /**
     * Constructs a new empty {@link LinkedHashMapWrapper}.
     *
     * @param property the {@link Property<Term>} that is used internally for equality checks and
     *        hash
     *        codes
     */
    public LinkedHashMapWrapper(Property<Term> property) {
        this.property = property;
        map = new LinkedHashMap<>();
    }

    /**
     * Constructs a new {@link LinkedHashMapWrapper} and inserts the given key-value pair.
     *
     * @param key the key to be inserted
     * @param value the value corresponding to {@code key}
     * @param property the {@link Property<Term>} that is used internally for equality checks and
     *        hash
     *        codes
     */
    public LinkedHashMapWrapper(Term key, V value, Property<Term> property) {
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
     *        hash
     *        codes
     */
    public LinkedHashMapWrapper(Term[] keys, V[] values, Property<Term> property) {
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
     *        hash
     *        codes
     */
    public LinkedHashMapWrapper(Iterable<Term> keys, Iterable<V> values, Property<Term> property) {
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
    public boolean containsKey(Term key) {
        return map.containsKey(wrapTerm(key));
    }

    /**
     * Returns the value to which the specified key is mapped, or {@code null} if this map contains
     * no mapping for the key.
     *
     * @param key the key whose associated value is to be returned
     * @return the value to which the specified key is mapped
     */
    public V get(Term key) {
        return map.get(wrapTerm(key));
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
    public V put(Term key, V value) {
        return map.put(wrapTerm(key), value);
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
    public void putAll(Term[] keys, V[] vals) {
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
    public void putAll(Iterable<Term> keys, Iterable<V> vals) {
        Iterator<V> itVals = vals.iterator();
        for (Term key : keys) {
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
    public V remove(Term key) {
        return map.remove(wrapTerm(key));
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
    public Iterator<TermPair<V>> iterator() {
        return new PairIterator<>(map);
    }

    /**
     * This helper method wraps a term in a {@link TermWrapper} with the {@link Property<Term>} of
     * this map.
     * <p>
     * This is done so that {@link EqualsModProperty} can be used for equality checks and hash
     * codes instead of the
     * usual {@code equals} and {@code hashCode} methods of {@link Term} in the internal
     * {@link LinkedHashMap}.
     *
     * @param term the term to be wrapped
     * @return the wrapped term
     */
    private TermWrapper wrapTerm(Term term) {
        return new TermWrapper(term, property);
    }


    // ------------- wrapper class for terms
    /**
     * This class is used to wrap a term and override the {@code equals} and {@code hashCode} methods for use in a
     * {@link LinkedHashMap}.
     * <p>
     * The wrapped term is equipped with a {@link Property<Term>} that is used for
     * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} and
     * {@link EqualsModProperty#hashCodeModProperty(Property)} )}.
     *
     * @param term     The term to be wrapped
     * @param property The {@link Property<Term>} that is used in the {@code equals} and {@code hashCode} methods
     */
    private record TermWrapper(Term term, Property<Term> property) {

    @Override
    public boolean equals(Object obj) {
        return term.equalsModProperty(obj, property);
    }

    @Override
    public int hashCode() {
        return term.hashCodeModProperty(property);
    }}

    // ------------- record for term-value mapping
    public record TermPair<V>(Term term, V value)
    {
    }

    // ------------- class to iterate over internal map and unwrap terms
    /**
     * This class is used to iterate over the key-value pairs in the {@link LinkedHashMapWrapper}.
     * <p>
     * The terms in the pairs are unwrapped before returning them.
     *
     * @param <V> the type of the values in the {@link LinkedHashMapWrapper}
     */
    private static class PairIterator<V> implements Iterator<TermPair<V>> {
        /**
         * The iterator over the keys of the internal map.
         */
        private final Iterator<TermWrapper> keyIt;

        /**
         * The internal map.
         */
        private final LinkedHashMap<TermWrapper, V> map;

        /**
         * The last key-value pair that was returned by {@link #next()}.
         */
        private TermWrapper last = null;

        /**
         * Creates a new iterator over the key-value pairs in the {@link LinkedHashMapWrapper}.
         *
         * @param map the internal map of the {@link LinkedHashMapWrapper} to iterate over
         */
        public PairIterator(final LinkedHashMap<TermWrapper, V> map) {
            this.map = map;
            keyIt = map.keySet().iterator();
        }

        @Override
        public boolean hasNext() {
            return keyIt.hasNext();
        }

        @Override
        public TermPair<V> next() {
            last = keyIt.next();
            return new TermPair<>(last.term(), map.get(last));
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
