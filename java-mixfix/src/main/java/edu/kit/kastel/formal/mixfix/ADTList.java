/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 * 
 * The system is protected by the GNU General Public License. 
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

import org.jspecify.annotations.NonNull;

import java.util.*;

/**
 * Lists as in the theory of Abstract Data Types.
 * <p>
 * In contrast to {@link java.util.List}, objects of this class are immutable.
 * New instances are returned by calls to {@link #cons(Object)}.
 * <p>
 * The list is implemented used a singly-linked list.
 * <p>
 * {@link ADTList} is iterable. The order of the iteration herein is
 * "newest elements first".
 * 
 * @author mattias ulbrich
 */
public class ADTList<T> implements Iterable<T> {

    /**
     * The value stored in this entry
     */
    private T head;

    /**
     * The remainder of the list.
     */
    private ADTList<T> tail;

    /**
     * The number of elements in this list. Is non-negative.
     */
    private final int size;

    /**
     * The Constant NIL is the only object with size == 0.
     */
    @SuppressWarnings({"rawtypes"})
    private static final ADTList NIL = new ADTList();

    public List<T> toList() {
        if(this==NIL){
            return new LinkedList<>();
        }
        var seq = tail.toList();
        seq.add(0, head);
        return seq;
    }

    /**
     * The private iterator class.
     */
    private static class It<T> implements Iterator<T> {

        /**
         * The current list element to take data from, may be NIL or null.
         */
        private ADTList<T> cur;

        /**
         * Instantiates a new it with a list object
         * 
         * @param adtList
         *            the list to iterate
         */
        public It(ADTList<T> adtList) {
            cur = adtList;
        }

        /**
         * {@inheritDoc}
         * 
         * If the current list is not null and has data, then the iterator has
         * more to iterate.
         */
        public boolean hasNext() {
            return cur != null && cur.size() > 0;
        }

        /**
         * {@inheritDoc}
         * 
         * If the iterator has more to iterate, return the head of the current
         * list and advance the list pointer to its tail.
         * <p>
         * Throw an exception if no data is available.
         */
        @Override
        public T next() {
            if (!hasNext())
                throw new NoSuchElementException();

            T t = cur.head;
            cur = cur.tail;
            return t;
        }

        /**
         * Not supported in this implementation.
         */
        @Override
        public void remove() {
            throw new UnsupportedOperationException(
                    "remove is not supported by this iterator.");
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Iterable#iterator()
     */
    @Override @NonNull
    public Iterator<T> iterator() {
        return new It<>(this);
    }

    /*
     * Used to create the NIL object
     */
    private ADTList() {
        size = 0;
    }

    /**
     * Instantiates a new list from an element another list.
     * 
     * @param head
     *            the element to set as head.
     * @param tail
     *            the list to use as tail.
     */
    public ADTList(T head, ADTList<T> tail) {
        this.head = head;
        this.size = tail.size + 1;
        this.tail = tail;
    }

    /**
     * Retrieves a type parametrised version of an empty list.
     * 
     * @return a reference to {@link #NIL}
     */
    @SuppressWarnings("unchecked")
    public static <T> ADTList<T> nil() {
        return NIL;
    }

    /**
     * Create a singleton list.
     * <p>
     * The resulting list has length 1 and contains the given element.
     * 
     * @param head
     *            the element to wrap in a singleton list.
     * 
     * @return a list of length 1.
     */
    public static <T> ADTList<T> singleton(T head) {
        return ADTList.<T> nil().cons(head);
    }

    /**
     * Create a new list from an element.
     * <p>
     * The new list's head is the element and its tail is <code>this</code>
     * list. Equivalent to calling <code>new ADTList&lt;T&gt;(head, this)</code>
     * .
     * 
     * @param head
     *            the element to add.
     * 
     * @return a list which is longer by one entry.
     */
    public ADTList<T> cons(T head) {
        return new ADTList<>(head, this);
    }

    /**
     * create a list which has element from the iterable collection added to
     * this list.
     * <p>
     * The collection is iterated and in that order the elements are added to
     * the new list.
     * 
     * @param collection
     *            the collection to add all elements from
     * 
     * @return a list which contains all elements from collection and from this.
     */
    public ADTList<T> consAll(Iterable<T> collection) {
        ADTList<T> result = this;
        for (T t : collection) {
            result = result.cons(t);
        }

        return result;
    }

    /**
     * Gets the data element stored in this list entry. May be null.
     * 
     * @return the head of the list
     */
    public T hd() {
        return head;
    }

    /**
     * Gets the remaining list referred to by this list. Is <code>null</code>
     * iff size==0.
     * 
     * @return the tail of the list.
     */
    public ADTList<T> tl() {
        return tail;
    }

    /**
     * Gets the number of elements stored in this list.
     * 
     * @return a non-negative number
     */
    public int size() {
        return size;
    }

    /**
     * Checks if this is empty.
     * <p>
     * Same as <code>size() == 0</code>.
     * 
     * @return true, iff is empty
     */
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     * Reverses the list.
     * 
     * @return a list with the same elements but in the opposite order.
     */
    public ADTList<T> rev() {
        return ADTList.<T> nil().consAll(this);
    }

    /**
     * {@inheritDoc}
     * 
     * This is equal to another {@link ADTList} if and only if their sizes are
     * equal, and they contain equal elements at each position
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof ADTList<?> list) {
            return size == list.size
                    && (Objects.equals(head, list.head))
                    && (Objects.equals(tail, list.tail));
        }
        return false;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     * @see java.util.List#toString()
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("[");
        Iterator<T> it = iterator();
        while (it.hasNext()) {
            sb.append(it.next());
            if (it.hasNext())
                sb.append(",");
        }
        sb.append("]");

        return sb.toString();
    }

}
