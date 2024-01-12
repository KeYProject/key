/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.Iterator;
import java.util.Map;

public class LinkedHashMap<K, V> extends java.util.LinkedHashMap<K, V>
        implements Iterable<Pair<K, V>> {


    private static final long serialVersionUID = 4295774122581786871L;

    public LinkedHashMap() {
        super();
    }


    public LinkedHashMap(Map<? extends K, ? extends V> m) {
        super(m);
    }


    public LinkedHashMap(K key, V value) {
        super();
        put(key, value);
    }


    public LinkedHashMap(K[] keys, V[] values) {
        super();
        putAll(keys, values);
    }


    public LinkedHashMap(Iterable<K> keys, Iterable<V> values) {
        super();
        putAll(keys, values);
    }


    public void putAll(K[] keys, V[] vals) {
        for (int i = 0; i < keys.length; i++) {
            if (i < vals.length) {
                put(keys[i], vals[i]);
            } else {
                put(keys[i], null);
            }
        }
    }


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

    public Iterator<Pair<K, V>> iterator() {
        return new PairIterator<>(this);
    }

    private static class PairIterator<K, V> implements Iterator<Pair<K, V>> {

        private final Iterator<K> keyIt;
        private final LinkedHashMap<K, V> map;
        private K last = null;

        public PairIterator(final LinkedHashMap<K, V> map) {
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
            return new Pair<>(last, map.get(last));
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
