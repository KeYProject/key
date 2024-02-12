/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import org.jspecify.annotations.Nullable;

import java.util.Iterator;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * An immutable data structure mapping keys to values. The map is not modified by any operation
 * after creation.
 *
 * @param <S> the type of keys for this map
 * @param <T> the type of contained mapped values
 */
public interface ImmutableMap<S extends @NonNull Object, T extends @Nullable Object>
        extends Iterable<ImmutableMapEntry<S, T>> {

    /**
     * Adds a mapping {@code <key, value>} to the map (old map is not modified)
     *
     * If the key exists, the old entry will be overwritten.
     *
     * @param key the key with which the specified value is to be associated
     * @param value the value to be associated with the specified key
     * @return the new mapping
     */
    ImmutableMap<S, T> put(S key, T value);

    /**
     * Retrieves the value mapped to the specified key in this map.
     *
     * @param key the key whose associated value is to be returned
     * @return the value to which the specified key is mapped, or {@code null} if this map contains
     *         no mapping for the key
     */
    @Nullable
    T get(S key);

    /**
     * Returns the number of entries in this map.
     *
     * @return the number of entries in this map
     */
    int size();

    /**
     * Returns {@code true} if this map contains no entries.
     *
     * @return {@code true} if this map contains no entries
     */
    boolean isEmpty();

    /**
     * Returns {@code true} if this map contains a mapping for the specified key.
     *
     * @param key the key whose presence in this map is to be tested
     * @return {@code true} if this map contains a mapping for the specified key
     */
    boolean containsKey(S key);

    /**
     * Returns {@code true} if this map maps one or more keys to the specified value.
     *
     * Comparison is modulo {@link Object#equals(Object)}.
     *
     * @param value the value whose presence in this map is to be tested
     * @return {@code true} if this map maps one or more keys to the specified value
     */
    boolean containsValue(T value);

    /**
     * Removes the mapping for a key from this map if it is present.
     *
     * @param key the key whose mapping is to be removed from the map
     * @return the new map (the same if the key is not in the map)
     */
    ImmutableMap<S, T> remove(S key);

    /**
     * Removes all mappings for the specified value from this map.
     *
     * Comparison is modulo {@link Object#equals(Object)}.
     *
     * @param value the value whose mappings are to be removed from the map
     * @return the new map (the same if the value is not mapped)
     */
    ImmutableMap<S, T> removeAll(T value);

    /**
     * Returns an iterator over the keys in this map.
     *
     * The order is most recent first.
     *
     * @return an iterator over the keys in this map
     */
    Iterator<S> keyIterator();

    /**
     * Returns an iterator over the values in this map.
     *
     * If a value is contained multiple times, it will be returned multiple times.
     * The order is most recent first.
     *
     * @return an iterator over the values in this map
     */
    Iterator<T> valueIterator();


    /**
     * Returns an iterator over the entries in this map.
     * The order is most recent first.
     *
     * @return an iterator over the entries in this map
     */
    Iterator<ImmutableMapEntry<S, T>> iterator();
}
