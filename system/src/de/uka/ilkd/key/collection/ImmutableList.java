// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.collection;

import java.util.Iterator;

/**
 * List interface to be implemented by non-destructive lists
 */
public interface ImmutableList<T> extends Iterable<T>, java.io.Serializable {

    /** prepends element to the list (non-destructive)
     * @param element the head of the created list
     * @return IList<T> with the new element as head and this list as tail
     */
    ImmutableList<T> prepend(T element);

    /** prepends a whole list (non-destructive)
     * @param list the list to be prepended
     * @return IList<T> list++this
     */

    ImmutableList<T> prepend(ImmutableList<T> list);
    
    /** prepends an iterable collection */
    ImmutableList<T> prepend(Iterable<T> collection);

    /** prepends array (O(n))
     * @param array the array of the elements to be prepended
     * @return IList<T> the new list
     */
    ImmutableList<T> prepend(T... array);

    /** appends element to the list (non-destructive)
     * @param element to be added at the end
     * @return IList<T> with the new element at the end
     */
    ImmutableList<T> append(T element);

    /** appends a whole list (non-destructive)
     * @param list the list to be appended
     * @return IList<T> this++list
     */
    ImmutableList<T> append(ImmutableList<T> list);
    
    /** appends an iterable collection */
    ImmutableList<T> append(Iterable<T> collection);

    /** appends element at end (non-destructive) (O(n))
     * @param array the array to be appended
     * @return IList<T> the new list
     */
    ImmutableList<T> append(T... array);

    /** @return <T> the first element in list */
    T head();

    /** @return IList<T> tail of list */

    ImmutableList<T> tail();

    /** @return IList<T> this list without the first <code>n</code> elements  */
    ImmutableList<T> take(int n);

    /**
     * Reverses this list
     */
    ImmutableList<T> reverse();

    /** @return Iterator<T> of this list */
    @Override
    Iterator<T> iterator();

    /** @return boolean is true iff. obj is in List */
    boolean contains(T obj);

    /** @return int representing number of elements in list  */

    int size();

    /** @return true iff the list is empty */
    boolean isEmpty();

    /** removes first occurrence of obj
     * @return new list
     */
    ImmutableList<T> removeFirst(T obj);

    /** removes all occurrences of obj
     * @return new list
     */
    ImmutableList<T> removeAll(T obj);

    /**
     * Convert the list to a Java array (O(n))
     */
    <S> S[] toArray(S[] array);
}

