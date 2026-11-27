/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.ui.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Objects;

/**
 * A {@link DefaultListModel} that keeps its elements sorted according to a comparator.
 * <p>
 * The model is backed by a sorted {@link ArrayList}. Positional insertion methods are not supported
 * because the order is defined by the comparator. Mutating the exposed backing list directly
 * bypasses sorting and event notification.
 *
 * @param <E> the type of the list elements
 */
public class SortedDefaultListModel<E> extends DefaultListModel<E> {
    private final Comparator<? super E> comparator;

    /**
     * Creates a sorted model using the given comparator.
     *
     * @param comparator the comparator defining the element order
     */
    public SortedDefaultListModel(Comparator<? super E> comparator) {
        this.comparator = Objects.requireNonNull(comparator);
    }

    /**
     * Creates a sorted model that uses the natural ordering of its elements. Elements must
     * implement {@link Comparable}.
     */
    @SuppressWarnings("unchecked")
    public SortedDefaultListModel() {
        this((Comparator<? super E>) Comparator.naturalOrder());
    }

    /**
     * Inserts an element at its sorted position.
     *
     * @param element the element to add
     */
    @Override
    public void addElement(E element) {
        super.add(insertionPoint(element), element);
    }

    /**
     * Positional insertion is not supported because the order is defined by the comparator.
     *
     * @throws UnsupportedOperationException always
     */
    @Override
    public void add(int index, E element) {
        throw new UnsupportedOperationException(
            "SortedDefaultListModel does not support positional insertion");
    }

    /**
     * Positional insertion is not supported because the order is defined by the comparator.
     *
     * @throws UnsupportedOperationException always
     */
    @Override
    public void insertElementAt(E element, int index) {
        throw new UnsupportedOperationException(
            "SortedDefaultListModel does not support positional insertion");
    }

    /**
     * Replaces an element and restores the sorted order.
     *
     * @param element the new element
     * @param index the index to replace
     */
    @Override
    public void setElementAt(E element, int index) {
        super.remove(index);
        addElement(element);
    }

    /**
     * Replaces an element and restores the sorted order.
     *
     * @param index the index to replace
     * @param element the new element
     * @return the previous element
     */
    @Override
    public E set(int index, E element) {
        E old = super.remove(index);
        addElement(element);
        return old;
    }

    /**
     * Adds all elements in sorted order.
     *
     * @param elements the elements to add
     * @return whether this model changed
     */
    @Override
    public boolean addAll(Collection<? extends E> elements) {
        boolean changed = false;
        for (E element : new ArrayList<>(elements)) {
            addElement(element);
            changed = true;
        }
        return changed;
    }

    /**
     * Returns the insertion index for an element, after all elements that compare as equal.
     *
     * @param element the element to insert
     * @return the sorted insertion index
     */
    private int insertionPoint(E element) {
        var list = getList();
        int index = Collections.binarySearch(list, element, comparator);
        if (index < 0) {
            return -index - 1;
        }
        while (index < list.size() && comparator.compare(list.get(index), element) == 0) {
            index++;
        }
        return index;
    }
}
