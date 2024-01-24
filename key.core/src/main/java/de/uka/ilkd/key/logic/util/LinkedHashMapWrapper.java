/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.util;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.equality.TermEqualsModProperty;
import de.uka.ilkd.key.logic.equality.TermProperty;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;


public class LinkedHashMapWrapper<V> {
    private final LinkedHashMap<TermWrapper, V> map;
    private final TermProperty property;

    public LinkedHashMapWrapper(TermProperty property) {
        this.property = property;
        map = new LinkedHashMap<>();
    }

    public LinkedHashMapWrapper(Term key, V value, TermProperty property) {
        this(property);
        put(key, value);
    }

    public LinkedHashMapWrapper(Term[] keys, V[] values, TermProperty property) {
        this(property);
        putAll(keys, values);
    }


    public LinkedHashMapWrapper(Iterable<Term> keys, Iterable<V> values, TermProperty property) {
        this(property);
        putAll(keys, values);
    }

    public int size() {
        return map.size();
    }

    public boolean isEmpty() {
        return map.isEmpty();
    }

    public boolean containsKey(Term key) {
        return map.containsKey(wrapTerm(key));
    }

    public V get(Term key) {
        return map.get(wrapTerm(key));
    }

    public V put(Term key, V value) {
        return map.put(wrapTerm(key), value);
    }

    public void putAll(Term[] keys, V[] vals) {
        for (int i = 0; i < keys.length; i++) {
            if (i < vals.length) {
                put(keys[i], vals[i]);
            } else {
                put(keys[i], null);
            }
        }
    }

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

    public V remove(Term key) {
        return map.remove(wrapTerm(key));
    }

    public boolean containsValue(V value) {
        return map.containsValue(value);
    }

    public Iterator<Pair<Term, V>> iterator() {
        return new PairIterator<>(map);
    }

    private TermWrapper wrapTerm(Term term) {
        return new TermWrapper(term, property);
    }


    // ------------- wrapper class for terms
    /**
     * This class is used to wrap a term and override the {@code equals} and {@code hashCode} methods for use in a
     * {@link LinkedHashMap}.
     * <p>
     * The wrapped term is equipped with a {@link TermProperty} that is used for
     * {@link TermEqualsModProperty#equalsModProperty(Object, TermProperty)} and
     * {@link TermEqualsModProperty#hashCodeModProperty(TermProperty)}.
     *
     * @param term     The term to be wrapped
     * @param property The {@link TermProperty} that is used in the {@code equals} and {@code hashCode} methods
     */
    private record TermWrapper(Term term, TermProperty property) {
        @Override
        public boolean equals(Object obj) {
            return term.equalsModProperty(obj, property);
        }

        @Override
        public int hashCode() {
            return term.hashCodeModProperty(property);
        }
    }

    // ------------- class to iterate over internal map and unwrap terms
    private static class PairIterator<V> implements Iterator<Pair<Term, V>> {

        private final Iterator<TermWrapper> keyIt;
        private final LinkedHashMap<TermWrapper, V> map;
        private TermWrapper last = null;

        public PairIterator(final LinkedHashMap<TermWrapper, V> map) {
            this.map = map;
            keyIt = map.keySet().iterator();
        }

        @Override
        public boolean hasNext() {
            return keyIt.hasNext();
        }

        @Override
        public Pair<Term, V> next() {
            last = keyIt.next();
            return new Pair<>(last.term(), map.get(last));
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
