/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.ui.util;

import java.util.*;
import javax.swing.AbstractListModel;

/**
 * A {@link javax.swing.ListModel} backed by an {@link ArrayList}. The backing list is exposed via
 * {@link #getList()}; modifications should still go through this model so that listeners are
 * notified.
 *
 * @param <E> the type of the list elements
 */
public class DefaultListModel<E> extends AbstractListModel<E> {
    private final ArrayList<E> list = new ArrayList<>();

    /**
     * Returns the backing list.
     *
     * @return the backing list
     */
    public List<E> getList() {
        return list;
    }

    /**
     * Returns the number of elements in this model.
     *
     * @return the number of elements
     */
    @Override
    public int getSize() {
        return list.size();
    }

    /**
     * Returns the element at the given index.
     *
     * @param index the index
     * @return the element at the index
     */
    @Override
    public E getElementAt(int index) {
        return list.get(index);
    }

    /**
     * Adds an element to the end of this model.
     *
     * @param element the element to add
     */
    public void addElement(E element) {
        add(list.size(), element);
    }

    /**
     * Inserts an element at the given index.
     *
     * @param index the insertion index
     * @param element the element to add
     */
    public void add(int index, E element) {
        list.add(index, element);
        fireIntervalAdded(this, index, index);
    }

    /**
     * Removes the first occurrence of the given element.
     *
     * @param element the element to remove
     * @return whether the element was found and removed
     */
    public boolean removeElement(Object element) {
        int index = list.indexOf(element);
        if (index < 0) {
            return false;
        }
        remove(index);
        return true;
    }

    /**
     * Removes the element at the given index.
     *
     * @param index the index to remove
     * @return the removed element
     */
    public E remove(int index) {
        E element = list.remove(index);
        fireIntervalRemoved(this, index, index);
        return element;
    }

    /**
     * Removes the element at the given index.
     *
     * @param index the index to remove
     */
    public void removeElementAt(int index) {
        remove(index);
    }

    /**
     * Inserts an element at the given index.
     *
     * @param element the element to insert
     * @param index the insertion index
     */
    public void insertElementAt(E element, int index) {
        add(index, element);
    }

    /**
     * Replaces the element at the given index.
     *
     * @param element the new element
     * @param index the index to replace
     */
    public void setElementAt(E element, int index) {
        list.set(index, element);
        fireContentsChanged(this, index, index);
    }

    /**
     * Removes all elements from this model.
     */
    public void removeAllElements() {
        clear();
    }

    /**
     * Removes all elements from this model.
     */
    public void clear() {
        int oldSize = list.size();
        if (oldSize == 0) {
            return;
        }
        list.clear();
        fireIntervalRemoved(this, 0, oldSize - 1);
    }

    /**
     * Returns the element at the given index.
     *
     * @param index the index
     * @return the element at the index
     */
    public E get(int index) {
        return list.get(index);
    }

    /**
     * Replaces the element at the given index.
     *
     * @param index the index to replace
     * @param element the new element
     * @return the previous element
     */
    public E set(int index, E element) {
        E old = list.set(index, element);
        fireContentsChanged(this, index, index);
        return old;
    }

    /**
     * Returns the number of elements in this model.
     *
     * @return the number of elements
     */
    public int size() {
        return list.size();
    }

    /**
     * Returns whether this model is empty.
     *
     * @return whether this model contains no elements
     */
    public boolean isEmpty() {
        return list.isEmpty();
    }

    /**
     * Returns whether the given element is contained in this model.
     *
     * @param element the element to look for
     * @return whether the element is contained
     */
    public boolean contains(Object element) {
        return list.contains(element);
    }

    /**
     * Returns the index of the first occurrence of the given element.
     *
     * @param element the element to look for
     * @return the index, or {@code -1} if the element is not contained
     */
    public int indexOf(Object element) {
        return list.indexOf(element);
    }

    /**
     * Returns the index of the last occurrence of the given element.
     *
     * @param element the element to look for
     * @return the index, or {@code -1} if the element is not contained
     */
    public int lastIndexOf(Object element) {
        return list.lastIndexOf(element);
    }

    /**
     * Returns the first element.
     *
     * @return the first element
     */
    public E firstElement() {
        return list.getFirst();
    }

    /**
     * Returns the last element.
     *
     * @return the last element
     */
    public E lastElement() {
        return list.getLast();
    }

    /**
     * Returns the element at the given index.
     *
     * @param index the index
     * @return the element at the index
     */
    public E elementAt(int index) {
        return list.get(index);
    }

    /**
     * Returns an enumeration over the elements of this model.
     *
     * @return an enumeration over the elements
     */
    public Enumeration<E> elements() {
        return Collections.enumeration(list);
    }

    /**
     * Copies the elements into the given array.
     *
     * @param array the destination array
     */
    public void copyInto(Object[] array) {
        for (int i = 0; i < list.size(); i++) {
            array[i] = list.get(i);
        }
    }

    /**
     * Returns the elements as an array.
     *
     * @return an array containing all elements
     */
    public Object[] toArray() {
        return list.toArray();
    }

    /**
     * Returns the elements as an array.
     *
     * @param array the destination array
     * @param <T> the array element type
     * @return an array containing all elements
     */
    public <T> T[] toArray(T[] array) {
        return list.toArray(array);
    }

    /**
     * Removes the elements in the given range.
     *
     * @param fromIndex the start index, inclusive
     * @param toIndex the end index, exclusive
     */
    public void removeRange(int fromIndex, int toIndex) {
        if (fromIndex > toIndex) {
            throw new IllegalArgumentException("fromIndex must not exceed toIndex");
        }
        if (fromIndex < 0 || toIndex > list.size()) {
            throw new ArrayIndexOutOfBoundsException();
        }
        if (fromIndex == toIndex) {
            return;
        }
        list.subList(fromIndex, toIndex).clear();
        fireIntervalRemoved(this, fromIndex, toIndex - 1);
    }

    /**
     * Adds all elements of the given collection.
     *
     * @param elements the elements to add
     * @return whether this model changed
     */
    public boolean addAll(Collection<? extends E> elements) {
        if (elements.isEmpty()) {
            return false;
        }
        int index = list.size();
        list.addAll(elements);
        fireIntervalAdded(this, index, list.size() - 1);
        return true;
    }
}
