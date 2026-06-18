/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.lang.ref.WeakReference;
import java.util.Collections;
import java.util.Map;
import java.util.WeakHashMap;
import java.util.function.Function;

/**
 * A thread-safe interner that guarantees a single canonical instance per key.
 *
 * <p>
 * KeY interns various derived objects (e.g. {@code ElementaryUpdate} per left-hand side,
 * sort-depending
 * functions per sort) so that equal objects are the <em>same</em> object and can be compared with
 * {@code ==}. The classic idiom &mdash; a {@code WeakHashMap<K, WeakReference<V>>} with a
 * get-then-create-then-put &mdash; is not thread-safe: under concurrency the map itself corrupts
 * and,
 * worse, two threads can create two distinct instances for the same key, silently breaking the
 * identity invariant. This class encapsulates that idiom correctly:
 * <ul>
 * <li><b>weak keys</b> (a {@link WeakHashMap}) so entries vanish once the key is unreachable;
 * <li><b>weak values</b> ({@link WeakReference}) so an interned instance can still be collected;
 * <li><b>atomic</b> get-or-create, so exactly one canonical instance exists per key.
 * </ul>
 *
 * @param <K> the key type
 * @param <V> the interned value type
 */
public final class WeakValueInterner<K, V> {

    private final Map<K, WeakReference<V>> instances =
        Collections.synchronizedMap(new WeakHashMap<>());

    /**
     * Returns the canonical instance for {@code key}, creating it with {@code factory} (and
     * interning it) if none exists yet (or the previously interned one has been collected).
     *
     * @param key the key
     * @param factory creates the value for a key on a cache miss; must not return {@code null}
     * @return the canonical value for {@code key}, identical for equal keys
     */
    public V intern(K key, Function<? super K, ? extends V> factory) {
        synchronized (instances) {
            WeakReference<V> ref = instances.get(key);
            V value = ref != null ? ref.get() : null;
            if (value == null) {
                value = factory.apply(key);
                instances.put(key, new WeakReference<>(value));
            }
            return value;
        }
    }
}
