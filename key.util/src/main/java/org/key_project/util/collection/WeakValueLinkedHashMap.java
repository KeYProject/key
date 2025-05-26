/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.LinkedHashMap;
import java.util.Objects;

import org.jspecify.annotations.Nullable;

/**
 * A map implementation that associates keys with weakly referenced values, preserving the order of
 * insertion.
 *
 * <p>
 * The {@code WeakValueLinkedHashMap} class stores values as weak references, allowing them to be
 * garbage-collected when they are no longer strongly reachable elsewhere. When a value is
 * garbage-collected, the associated key-value pair is automatically removed from the map. The map
 * maintains the insertion order of entries, similar to {@link LinkedHashMap}.
 * </p>
 *
 * <p>
 * This class is suitable for use cases where memory efficiency is a concern and it is acceptable to
 * lose entries when values are no longer in use.
 * </p>
 *
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of values stored in the map
 */
public class WeakValueLinkedHashMap<K, V> {

    private final LinkedHashMap<K, KeyWeakValuePair<K, V>> delegate = new LinkedHashMap<>();
    private final ReferenceQueue<V> queue = new ReferenceQueue<>();

    /**
     * Associates the specified key with the specified value in this map. If the map previously
     * contained a mapping for the key, the old value is replaced.
     *
     * <p>
     * Entries with garbage-collected values are automatically removed before adding the new entry.
     * </p>
     *
     * @param key the key with which the specified value is to be associated
     * @param value the value to be associated with the specified key
     * @return the previous value associated with the key, or {@code null} if there was no mapping
     *         for the key
     */
    public @Nullable V put(K key, @Nullable V value) {
        removeEntriesWithGCValues();
        final var weakVal = new KeyWeakValuePair<>(key, value, queue);
        var previous = delegate.put(key, weakVal);
        return previous != null ? previous.get() : null;
    }

    /**
     * Returns the value to which the specified key is mapped, or {@code null} if this map contains
     * no mapping for the key.
     *
     * @param key the key whose associated value is to be returned
     * @return the value to which the specified key is mapped, or {@code null} if no mapping exists
     */
    public @Nullable V get(K key) {
        var result = delegate.get(key);
        return result == null ? null : result.get();
    }

    /**
     * <p>
     * Returns {@code true} if this map contains a mapping for the specified key.
     * </p>
     *
     * <p>
     * Entries with garbage-collected values are automatically removed before checking for the key.
     * </p>
     *
     * @param key the key whose presence in this map is to be tested
     * @return {@code true} if this map contains a mapping for the specified key, otherwise
     *         {@code false}
     */
    public boolean containsKey(K key) {
        removeEntriesWithGCValues();
        return delegate.containsKey(key);
    }

    /**
     * Internal method to remove entries whose values have been garbage-collected.
     *
     * <p>
     * This method is called automatically during operations like {@code put} and
     * {@code containsKey} to ensure the map remains up-to-date.
     * </p>
     */
    private void removeEntriesWithGCValues() {
        KeyWeakValuePair<K, V> gcValue;
        while ((gcValue = (KeyWeakValuePair<K, V>) queue.poll()) != null) {
            delegate.remove(gcValue.key);
        }
    }

    /**
     * A weak reference that associates a key with its corresponding value.
     *
     * <p>
     * This class is used internally by {@code WeakValueLinkedHashMap} to hold the values as
     * weak references and track the associated keys for removal when values are garbage-collected.
     *
     * @param <K> the type of key
     * @param <V> the type of value
     */
    final static class KeyWeakValuePair<K, V> extends WeakReference<V> {
        final K key;

        /**
         * Constructs a new {@code KeyWeakValuePair}.
         *
         * @param key the key associated with the value
         * @param value the value to be weakly referenced
         * @param queue the reference queue to which this reference will be appended after garbage
         *        collection
         */
        public KeyWeakValuePair(K key, @Nullable V value, ReferenceQueue<V> queue) {
            super(value, queue);
            this.key = key;
        }

        /**
         * Compares this {@code KeyWeakValuePair} with another object for equality.
         *
         * <p>
         * Two {@code KeyWeakValuePair} objects are considered equal if their keys are equal
         * and their values are equal or both {@code null}.
         *
         * @param other the object to compare with
         * @return {@code true} if the objects are equal, otherwise {@code false}
         */
        @Override
        public boolean equals(@Nullable Object other) {
            if (this == other)
                return true;
            if (!(other instanceof KeyWeakValuePair<?, ?> weakVal)) {
                return false;
            }
            return Objects.equals(get(), weakVal.get());
        }

    }

}
