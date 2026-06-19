/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Set;

import org.jspecify.annotations.Nullable;

/**
 * Hash set using the object's identity instead of their hashcode to determine uniqueness.
 *
 * @param <T> elmeent type
 * @author Arne Keller
 */
public final class IdentityHashSet<T extends @Nullable Object> implements Set<T> {
    /**
     * Backing store.
     */
    private final IdentityHashMap<T, @Nullable Object> innerMap = new IdentityHashMap<>();

    /**
     * Construct an empty set.
     */
    public IdentityHashSet() {

    }

    /**
     * Copy provided elements into a new set.
     *
     * @param list elements to add
     */
    public IdentityHashSet(ImmutableList<T> list) {
        list.forEach(this::add);
    }

    @Override
    public int size() {
        return innerMap.size();
    }

    @Override
    public boolean isEmpty() {
        return innerMap.isEmpty();
    }

    @Override
    public boolean contains(@Nullable Object o) {
        return innerMap.containsKey(o);
    }

    @Override
    public Iterator<T> iterator() {
        return innerMap.keySet().iterator();
    }

    // see https://eisop.github.io/cf/manual/manual.html#nullness-collection-toarray
    @SuppressWarnings({ "nullness", "override.return.invalid" })
    @Override
    public @Nullable Object[] toArray() {
        return innerMap.keySet().toArray();
    }

    // see https://eisop.github.io/cf/manual/manual.html#nullness-collection-toarray
    @SuppressWarnings({ "nullness", "override.return.invalid" })
    @Override
    public <T> T[] toArray(T[] a) {
        return innerMap.keySet().toArray(a);
    }

    @Override
    public boolean add(T o) {
        return innerMap.put(o, o) == null;
    }

    @Override
    public boolean remove(@Nullable Object o) {
        var contained = innerMap.containsKey(o);
        innerMap.remove(o);
        return contained;
    }

    @Override
    public boolean addAll(Collection<? extends T> c) {
        var changed = false;
        for (T o : c) {
            changed |= add(o);
        }
        return changed;
    }

    @Override
    public void clear() {
        innerMap.clear();
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        var changed = false;
        for (Object o : c) {
            changed |= remove(o);
        }
        return changed;
    }



    @Override
    public boolean retainAll(Collection<?> c) {
        return innerMap.keySet().retainAll(c);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return innerMap.keySet().containsAll(c);
    }
}
