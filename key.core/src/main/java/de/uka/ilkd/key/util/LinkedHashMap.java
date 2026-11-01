/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.util;

import java.util.Iterator;
import java.util.Map;

import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * An insertion-ordered map that exposes its entries as an {@link Iterable} of
 * {@link Pair}s.
 *
 * <p>
 * The {@code implements Iterable<Pair<K, V>>} clause is rejected by the checker only in the
 * full-module pass, where the unannotated {@code Pair} carries {@code KeyFor}-system bounds
 * ({@code K}/{@code V} get the bottom bound {@code @KeyForBottom NullType}); the map's
 * entries legitimately stay {@code @UnknownKeyFor}, so the diagnostic is suppressed with a
 * scoped key at class level.
 */
@NullMarked
@SuppressWarnings("nullness:type.argument.type.incompatible")
public class LinkedHashMap<K, V> extends java.util.LinkedHashMap<K, V>
        implements Iterable<Pair<K, V>> {


    private static final long serialVersionUID = 4295774122581786871L;

    public LinkedHashMap() {
        super();
    }


    public LinkedHashMap(Map<? extends K, ? extends V> m) {
        super(m);
    }


    /**
     * The seed insertion operates on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here because the map is empty at this
     * point and {@link #put} only stores into it, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public LinkedHashMap(K key, V value) {
        super();
        put(key, value);
    }


    /**
     * The seed insertion operates on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here because the map is empty at this
     * point and {@link #putAll} only stores into it, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public LinkedHashMap(K[] keys, V[] values) {
        super();
        putAll(keys, values);
    }


    /**
     * The seed insertion operates on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here because the map is empty at this
     * point and {@link #putAll} only stores into it, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public LinkedHashMap(Iterable<K> keys, Iterable<V> values) {
        super();
        putAll(keys, values);
    }


    /**
     * Copies the key/value pairs from the given arrays. A key without a corresponding value
     * (i.e. {@code i >= vals.length}) is stored with a {@code null} value as a deliberate
     * "missing value" marker. The map therefore genuinely tolerates {@code null} values even
     * though the generic type {@code V} is non-null; the {@code put(..., null)} below is
     * suppressed because the {@code null} is an intentional value, not an error.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
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
     * Copies the key/value pairs from the given iterables; a key with no remaining value in
     * {@code vals} is stored with a {@code null} value as a deliberate "missing value" marker
     * (see {@link #putAll(Object[], Object[])}). The map therefore genuinely tolerates
     * {@code null} values even though the generic type {@code V} is non-null; the
     * {@code put(..., null)} below is suppressed because the {@code null} is intentional.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
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
        /** The key returned by the last {@link #next()}, or {@code null} before the first call. */
        private @Nullable K last = null;

        public PairIterator(final LinkedHashMap<K, V> map) {
            this.map = map;
            keyIt = map.keySet().iterator();
        }

        @Override
        public boolean hasNext() {
            return keyIt.hasNext();
        }

        /**
         * The pair's second component may legitimately be {@code null}: the map stores
         * {@code null} as a "missing value" marker for keys without a value (see
         * {@code putAll(K[], V[])}), so {@link Map#get} yields a nullable value. The
         * {@link Pair} constructor, however, demands a non-null value; the value argument is
         * suppressed because a {@code null} value is part of the map's documented contract
         * (the key argument is a freshly read, provably non-null local).
         */
        @SuppressWarnings("nullness:argument.type.incompatible")
        @Override
        public Pair<K, V> next() {
            K nextKey = keyIt.next();
            last = nextKey;
            return new Pair<K, V>(nextKey, map.get(nextKey));
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
