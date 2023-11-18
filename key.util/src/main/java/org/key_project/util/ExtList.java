/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;


import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.jspecify.annotations.Nullable;


/**
 * extends java.util.LinkedList in order to collect elements
 * according to their type.
 *
 * @deprecated This class provides a bad coding style of exploiting reflection in the construction
 *             of KeY-Java-AST.
 *             Will be removed.
 */
@Deprecated
public class ExtList extends ArrayList<Object> {
    public ExtList() {
        super();
    }

    public ExtList(Object[] a) {
        addAll(Arrays.asList(a));
    }

    public ExtList(int size) {
        super(size);
    }

    /**
     * copies list to array (array has type of cl)
     */
    private static <T> T[] toArray(Class<T> cl, List<T> list) {
        @SuppressWarnings("unchecked")
        T[] array = (T[]) java.lang.reflect.Array.newInstance(cl, list.size());
        System.arraycopy(list.toArray(), 0, array, 0, list.size());
        return array;
    }

    /**
     * collects (non-null) elements of the classtype cl and returns a typed array
     *
     * @param cl Class the type of the elements that are selected
     * @return array with type cl
     */
    @SuppressWarnings("unchecked")
    public <T> T[] collect(Class<T> cl) {
        List<T> colls = new ArrayList<>(size());
        for (Object next : this) {
            if (cl.isInstance(next) && (next != null)) {
                colls.add((T) next);
            }
        }

        return toArray(cl, colls);
    }

    public <T> List<T> collectList(Class<T> cl) {
        List<T> colls = new ArrayList<>(size());
        for (Object next : this) {
            if (cl.isInstance(next) && (next != null)) {
                colls.add((T) next);
            }
        }
        return colls;
    }


    /**
     * returns first element in list of type cl
     *
     * @param cl the type to be searched in list
     * @return the first element with type cl in list
     */
    @SuppressWarnings("unchecked")
    @Nullable
    public <T> T get(Class<T> cl) {
        for (Object next : this) {
            if (cl.isInstance(next) && (next != null)) {
                return (T) next;
            }
        }

        return null;
    }

    /**
     * returns first element in list of type cl and removes the found
     * element from the list if the elemnt has not been found <tt>null</tt>
     * is returned
     *
     * @param cl the type to be searched in list
     * @return the first element with type cl in list
     */
    @SuppressWarnings("unchecked")
    public <T> T removeFirstOccurrence(Class<T> cl) {
        Iterator<Object> it = iterator();
        while (it.hasNext()) {
            Object next = it.next();
            if (cl.isInstance(next) && (next != null)) {
                it.remove();
                return (T) next;
            }
        }

        return null;
    }

    public Object getFirst() {
        return get(0);
    }

    public void addFirst(Object o) {
        add(0, o);
    }

    public Object removeFirst() {
        return remove(0);
    }
}
