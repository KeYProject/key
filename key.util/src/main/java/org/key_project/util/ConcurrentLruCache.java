/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

import org.jspecify.annotations.Nullable;

/**
 * A thread-safe {@link LRUCache} with <em>exact</em> least-recently-used eviction order.
 *
 * <p>
 * This is a single-lock cache: every operation (including {@link #get}, which reorders the access
 * recency) is serialized on the cache instance. That makes it a behaviour-preserving, drop-in
 * replacement for the {@code Collections.synchronizedMap(new LRUCache<>(n))} idiom -- it delegates
 * to exactly that, only behind a named, reusable type with an atomic {@link #computeIfAbsent}.
 *
 * <p>
 * Use this flavour when the eviction order matters for correctness, i.e. when a cached value
 * depends
 * on <em>when</em> it was first computed (KeY has such caches -- e.g. the introduction-time cache,
 * whose value reflects the goal history at first-cache time). For such caches an approximate or
 * striped eviction policy would change proofs, so the exact, fully-serialized order is mandatory.
 * For caches whose value is a pure function of the key (eviction only affects the hit rate, never
 * the result), prefer {@link StripedLruCache}, which trades exact global order for far lower lock
 * contention.
 *
 * <p>
 * The collection views ({@link #keySet()}, {@link #values()}, {@link #entrySet()}) inherit the
 * {@code Collections.synchronizedMap} contract: iterating them must be done while synchronizing on
 * this cache instance.
 *
 * @param <K> the key type
 * @param <V> the value type
 */
// keyfor: this is a faithful delegate of Collections.synchronizedMap; the @KeyFor relationships the
// Map interface declares (on put/keySet/values/entrySet) cannot be expressed across the delegation.
// Null-safety is unaffected -- the nullable returns are annotated below.
@SuppressWarnings({ "keyfor", "override.return.invalid" })
public final class ConcurrentLruCache<K, V> implements Map<K, V> {

    private final Map<K, V> delegate;

    /**
     * Creates a thread-safe exact-LRU cache holding at most {@code maxEntries} entries.
     *
     * @param maxEntries the maximum number of entries before the least recently used one is evicted
     */
    public ConcurrentLruCache(int maxEntries) {
        this.delegate = Collections.synchronizedMap(new LRUCache<>(maxEntries));
    }

    @Override
    public @Nullable V get(Object key) {
        return delegate.get(key);
    }

    @Override
    public @Nullable V put(K key, V value) {
        return delegate.put(key, value);
    }

    @Override
    public @Nullable V computeIfAbsent(K key,
            Function<? super K, ? extends @Nullable V> mappingFunction) {
        return delegate.computeIfAbsent(key, mappingFunction);
    }

    @Override
    public @Nullable V computeIfPresent(K key,
            BiFunction<? super K, ? super V, ? extends @Nullable V> remappingFunction) {
        return delegate.computeIfPresent(key, remappingFunction);
    }

    @Override
    public @Nullable V compute(K key,
            BiFunction<? super K, ? super @Nullable V, ? extends @Nullable V> remappingFunction) {
        return delegate.compute(key, remappingFunction);
    }

    @Override
    public @Nullable V putIfAbsent(K key, V value) {
        return delegate.putIfAbsent(key, value);
    }

    @Override
    public @Nullable V remove(Object key) {
        return delegate.remove(key);
    }

    @Override
    public void putAll(Map<? extends K, ? extends V> m) {
        delegate.putAll(m);
    }

    @Override
    public void clear() {
        delegate.clear();
    }

    @Override
    public int size() {
        return delegate.size();
    }

    @Override
    public boolean isEmpty() {
        return delegate.isEmpty();
    }

    @Override
    public boolean containsKey(Object key) {
        return delegate.containsKey(key);
    }

    @Override
    public boolean containsValue(Object value) {
        return delegate.containsValue(value);
    }

    @Override
    public @Nullable V getOrDefault(Object key, V defaultValue) {
        return delegate.getOrDefault(key, defaultValue);
    }

    @Override
    public Set<K> keySet() {
        return delegate.keySet();
    }

    @Override
    public Collection<V> values() {
        return delegate.values();
    }

    @Override
    public Set<Entry<K, V>> entrySet() {
        return delegate.entrySet();
    }

    /**
     * The lock that guards this cache. Synchronize on it (not on this instance) when iterating one
     * of the collection views, mirroring the {@code Collections.synchronizedMap} contract.
     *
     * @return the monitor to hold while iterating a view
     */
    public Object mutex() {
        return delegate;
    }
}
