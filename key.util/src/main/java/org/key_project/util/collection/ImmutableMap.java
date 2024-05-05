/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Iterator;


/**
 * This interface has to be implemented by a Class providing a persistent Map.
 */
public interface ImmutableMap<S, T>
        extends Iterable<ImmutableMapEntry<S, T>> {

    /**
     * adds a mapping {@code <key,val>} to the Map (old map is not modified) if key exists old entry
     * has to
     * be removed
     *
     * @return the new mapping
     */
    ImmutableMap<S, T> put(S key, T value);

    /** @return value of type <T> that is mapped by key of type<S> */
    T get(S key);

    /** @return number of entries as int */
    int size();

    /** @return true iff the map is empty */
    boolean isEmpty();

    /** @return true iff the map includes key */
    boolean containsKey(S key);

    /** @return true iff the map includes value */
    boolean containsValue(T value);

    /**
     * removes mapping (key,...) from map
     *
     * @return the new map (the same if key is not in the map)
     */
    ImmutableMap<S, T> remove(S key);

    /**
     * removes all mappings (...,value) from map
     *
     * @return the new map (the same if value is not mapped)
     */
    ImmutableMap<S, T> removeAll(T value);

    /** @return iterator about all keys */
    Iterator<S> keyIterator();

    /** @return iterator about all values */
    Iterator<T> valueIterator();

    /** @return iterator for entries */
    Iterator<ImmutableMapEntry<S, T>> iterator();


}
