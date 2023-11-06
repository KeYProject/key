/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;


import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;


/**
 * Extends java.util.LinkedList in order to collect elements according to their type.
 * Has facilities to get elements of a certain type ({@link #get(Class)}, {@link #collect(Class)}).
 */
public class ExtList extends LinkedList<Object> {

    private static final long serialVersionUID = 9182017368310263908L;

    public ExtList() {
        super();
    }

    public ExtList(Object[] a) {
        super();
        this.addAll(Arrays.asList(a));
    }

    /** copies list to array (array has type of cl) */
    private static <T> T[] toArray(Class<T> cl, LinkedList<T> list) {
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
        LinkedList<T> colls = new LinkedList<>();
        for (Object next : this) {
            if (cl.isInstance(next) && (next != null)) {
                colls.add((T) next);
            }
        }

        return toArray(cl, colls);

    }

    /**
     * returns first element in list of type cl
     *
     * @param cl the type to be searched in list
     * @return the first element with type cl in list
     */
    @SuppressWarnings("unchecked")
    public <T> T get(Class<T> cl) {
        for (Object next : this) {
            if (cl.isInstance(next) && (next != null)) {
                return (T) next;
            }
        }

        return null;
    }

    /**
     * returns first element in list of type cl and removes the found element from the list if the
     * elemnt has not been found <tt>null</tt> is returned
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


}
