/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

import org.jspecify.annotations.Nullable;

/**
 * A bounded cache that several threads can use at the same time, with one <em>exact</em>
 * least-recently-used eviction order.
 *
 * <p>
 * Vocabulary, in one paragraph: a <em>cache</em> stores results of a computation so they do not
 * have to be computed again; <em>bounded</em> means it holds at most a fixed number of entries;
 * when it is full and a new entry arrives, the entry that has not been used for the longest time
 * is thrown out (<em>least recently used</em>, LRU, <em>eviction</em>); <em>thread-safe</em> means
 * several threads may call any method at any time without corrupting the cache -- important in
 * KeY because the multi-core prover runs proof search on several worker threads that all see the
 * same cache.
 *
 * <p>
 * This class achieves thread safety with a single lock: every operation, even a plain
 * {@link #get} (which counts as a "use" and therefore changes the LRU order), waits for that one
 * lock. All threads queue up at the same lock, which costs speed but buys one guarantee that
 * {@link StripedLruCache} cannot give: there is one exact LRU order over <em>all</em> entries, so
 * <em>which</em> entry is evicted, and when, is fully deterministic.
 *
 * <p>
 * <b>Which of the two caches do I need?</b> Ask: <em>"if this entry were thrown away and computed
 * again later, could the new value be different?"</em>
 * <ul>
 * <li>Yes, the value depends on when it was first stored &rarr; use this class. Example from KeY:
 * a cache that stores at which proof step a formula was first seen. Recomputing that later would
 * store a <em>different</em> (later) step, so losing an entry changes results -- eviction must
 * follow one exact, reproducible order.</li>
 * <li>No, the value only depends on the key (same key &rarr; always the same value) &rarr; use
 * {@link StripedLruCache}. Losing an entry there only costs time, never correctness, so it can
 * drop the single global lock and run much faster under many threads.</li>
 * </ul>
 *
 * <p>
 * Implementation: an access-ordered {@link LinkedHashMap} with size-bounded eviction, wrapped in
 * {@code Collections.synchronizedMap}, behind a named, reusable type with an atomic
 * {@link #computeIfAbsent}.
 *
 * <p>
 * The collection views ({@link #keySet()}, {@link #values()}, {@link #entrySet()}) inherit the
 * {@code Collections.synchronizedMap} contract: iterating them must be done while synchronizing on
 * {@link #mutex()} (the underlying synchronized map), not on this cache instance.
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
        this.delegate =
            Collections.synchronizedMap(new LinkedHashMap<>(maxEntries + 1, 1.0F, true) {
                @Override
                protected boolean removeEldestEntry(Map.Entry<K, V> eldest) {
                    return size() > maxEntries;
                }
            });
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

    /*
     * The remaining java.util.Map default methods must be overridden too: the interface defaults
     * compose individually-synchronized calls into non-atomic check-then-act sequences, silently
     * breaking this class's "every operation is serialized" contract. The synchronizedMap
     * delegate's own implementations are atomic on the shared mutex.
     */

    @Override
    public @Nullable V merge(K key, V value,
            BiFunction<? super V, ? super V, ? extends @Nullable V> remappingFunction) {
        return delegate.merge(key, value, remappingFunction);
    }

    @Override
    public boolean remove(Object key, Object value) {
        return delegate.remove(key, value);
    }

    @Override
    public @Nullable V replace(K key, V value) {
        return delegate.replace(key, value);
    }

    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        return delegate.replace(key, oldValue, newValue);
    }

    @Override
    public void forEach(BiConsumer<? super K, ? super V> action) {
        delegate.forEach(action);
    }

    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        delegate.replaceAll(function);
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
