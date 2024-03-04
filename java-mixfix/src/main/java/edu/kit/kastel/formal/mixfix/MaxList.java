/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 * 
 * The system is protected by the GNU General Public License. 
 * See LICENSE.TXT for details.
 */

package edu.kit.kastel.formal.mixfix;

import java.util.AbstractList;
import java.util.List;

/**
 * The MaxList is a wrapper around an arbitrary {@link List} object which
 * records reading accesses and allows to query for the maximum index to be
 * read.
 *
 * @author mattias ulbrich
 */
public class MaxList<E> extends AbstractList<E> {
    
    /**
     * The wrapped list.
     */
    private final List<E> wrappedList;
    /**
     * The maximum index read so far. -1 indicates that no entry has been read
     * yet.
     */
    private int maxIndex = -1;
    
    /**
     * Gets the maximum index read so far.
     *
     * -1 is returned if no reading has been done yet from this list.
     *
     * @return an integer value greater or equal to -1.
     */
    public int getMaxReadIndex() {
        return maxIndex;
    }

    /**
     * Instantiates a new max list by w
     *
     * @param wrappedList
     *            the wrapped list
     */
    public MaxList(List<E> wrappedList) {
        this.wrappedList = wrappedList;
    }

    /* (non-Javadoc)
     * @see java.util.AbstractList#get(int)
     */
    @Override
    public E get(int index) {
        maxIndex = Math.max(index, maxIndex);
        return wrappedList.get(index);
    }

    /* (non-Javadoc)
     * @see java.util.AbstractCollection#size()
     */
    @Override
    public int size() {
        return wrappedList.size();
    }

}
