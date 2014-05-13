// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.collection;

import java.util.Iterator;


/**
 * Interface for heaps of objects of class T. T has to implement the
 * interface <code>Comparable</code>, and the heap is able to return
 * the minimum member regarding the relation <code>compareTo</code> of
 * T via the method <code>findMin</code>. Elements of the interface
 * <code>Heap<T></code> are immutable. Implementations of
 * <code>Heap<T></code> have to provide an attribute
 * <code>EMPTY_HEAP</code>, which is a singleton representing empty
 * heaps. Heaps may contain multiple references to one object, or
 * multiple objects which are <code>equal</code>.
 */
public interface ImmutableHeap<T extends Comparable<T>> extends java.io.Serializable {

    /**
     * @return true iff this heap is empty
     */
    boolean isEmpty ();

    /**
     * Add an element to this heap object
     * @param element The element to be added
     * @return a heap that contains all elements of this heap, and
     * additionally <code>element</code>
     */
    ImmutableHeap<T> insert ( T element );

    /**
     * Add multiple elements to this heap object
     * @param elements The elements to be added
     * @return a heap that contains all elements of this heap, and
     * additionally all objects from <code>elements</code>
     */
    ImmutableHeap<T> insert ( Iterator<T> elements );

    /**
     * Add multiple elements to this heap object
     * @param h a heap containing the elements to be added
     * @return a heap that contains all elements of this heap, and
     * additionally all objects from <code>h</code>
     */
    ImmutableHeap<T> insert ( ImmutableHeap<T> h );

    /**
     * @return the minimum element of this heap, or null iff this heap
     * is empty (<code>isEmpty()==true</code>)
     */
    T findMin ();

    /**
     * Remove the minimum element from this heap
     * @return a heap that contains all elements of this heap except
     * for the minimum element
     */
    ImmutableHeap<T> deleteMin ();

    /**
     * Remove all elements of this heap which are <code>equal</code>
     * to <code>element</code>.
     * @return heap that has all occurrences of <code>element</code>
     * removed
     */
    ImmutableHeap<T> removeAll ( T element );

    /**
     * @return the number of elements this heap holds
     */
    int size ();

    /**
     * @return an iterator that returns all elements of this heap
     */
    Iterator<T> iterator ();

    /**
     * @return an iterator that returns all elements of this heap in
     * increasing order
     */
    Iterator<T> sortedIterator ();

}