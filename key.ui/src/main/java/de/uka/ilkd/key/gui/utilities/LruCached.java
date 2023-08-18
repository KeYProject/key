/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.util.function.Function;

import org.key_project.util.LRUCache;

/**
 * Caches a computation using a lru cache
 *
 * @param <A> arguments for the computation
 * @param <T> return type
 */
public class LruCached<A, T> {
    private final LRUCache<A, T> lru = new LRUCache<>(32);
    private final Function<A, T> update;

    /**
     * Constructor
     *
     * @param update the computation
     */
    public LruCached(Function<A, T> update) {
        this.update = update;
    }

    /**
     * Gets a possibly cached value
     *
     * @param args the arguments
     * @return the value
     */
    public T get(A args) {
        T value = lru.get(args);
        if (value != null) {
            return value;
        }
        value = update.apply(args);
        lru.put(args, value);
        return value;
    }
}
