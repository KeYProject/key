/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Collection;
import java.util.LinkedHashMap;

/**
 * A copy-on-write map used for the {@link TacletIndex}'s find-taclet lists. {@link #copy()} shares
 * the backing map in O(1); the first mutating call ({@link #put}/{@link #remove}) clones it, so a
 * shared map is never written in place. Reads delegate straight through.
 *
 * <p>
 * The point is memory: every proof {@link Goal} gets its own {@link TacletIndex} via
 * {@link TacletIndex#copy()}, but the find-taclet lists are only changed by a few operations
 * (\addrules, program-variable renaming). Sharing until first write means the (large) base index is
 * physically duplicated only when a goal actually modifies it, instead of on every branch.
 *
 * <p>
 * The backing map is a {@link LinkedHashMap}, so iteration order (hence taclet-match order and
 * proof search) is unchanged. Not strictly thread-safe, but a shared map is only read while a
 * writer clones away from it -- benign (at worst a redundant clone).
 *
 * @param <K> key type
 * @param <V> value type
 */
final class CopyOnWriteIndexMap<K, V> {
    private LinkedHashMap<K, V> map;
    /**
     * {@code true} while {@link #map} may be shared with another instance (see {@link #copy()}).
     */
    private boolean shared;

    CopyOnWriteIndexMap() {
        this.map = new LinkedHashMap<>();
    }

    private CopyOnWriteIndexMap(LinkedHashMap<K, V> sharedMap) {
        this.map = sharedMap;
        this.shared = true;
    }

    /**
     * Returns a copy that shares this map's backing store until one of them is written. O(1).
     */
    CopyOnWriteIndexMap<K, V> copy() {
        this.shared = true;
        return new CopyOnWriteIndexMap<>(this.map);
    }

    /** Take a private copy of the backing map before a write, if it is currently shared. */
    private void ensureExclusive() {
        if (shared) {
            map = new LinkedHashMap<>(map);
            shared = false;
        }
    }

    V get(Object key) {
        return map.get(key);
    }

    Collection<V> values() {
        return map.values();
    }

    V put(K key, V value) {
        ensureExclusive();
        return map.put(key, value);
    }

    V remove(Object key) {
        ensureExclusive();
        return map.remove(key);
    }
}
