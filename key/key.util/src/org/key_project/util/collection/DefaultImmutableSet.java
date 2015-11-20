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

package org.key_project.util.collection;

import java.util.ArrayList;
import java.util.Iterator;

/**
 * implementation of a persistent set using the SLListOf<T> implementation with
 * all its implications (means e.g. O(n) for adding an element and so on.
 */
public class DefaultImmutableSet<T> implements ImmutableSet<T> {

    /**
     *
     */
    private static final long serialVersionUID = -5000602574000532257L;

    /** list containing the elements */
    private final ImmutableList<T> elementList;

    /** the empty set */
    @SuppressWarnings("unchecked")
    public static final <T> DefaultImmutableSet<T> nil() {
        return (DefaultImmutableSet<T>) NILSet.NIL;
    }

    protected DefaultImmutableSet() {
        elementList = ImmutableSLList.<T> nil();
    }

    /**
     * creates new set with one element
     * 
     * @param element
     *            of type <T> the new Set contains
     */
    protected DefaultImmutableSet(T element) {
        elementList =
                (ImmutableList<T>) (ImmutableSLList.<T> nil()).prepend(element);
    }

    /**
     * creates new set containg all elements from the elementList PRECONDITION:
     * elementList has no duplicates
     * 
     * @param elementList
     *            IList<T> contains all elements of the new Set
     */
    private DefaultImmutableSet(ImmutableList<T> elementList) {
        this.elementList = elementList;
    }

    /**
     * adds an element
     * 
     * @param element
     *            of type <T> that has to be added to this set
     */
    public ImmutableSet<T> add(T element) {
        if (elementList.contains(element)) {
            return this;
        }
        return new DefaultImmutableSet<T>(elementList.prepend(element));
    }

    /**
     * adds an element, barfs if the element is already present
     * 
     * @param element
     *            of type <T> that has to be added to this set
     * @throws org.key_project.utils.collection.NotUniqueException
     *             if the element is already present
     */
    public ImmutableSet<T> addUnique(T element) throws NotUniqueException {
        if (elementList.contains(element)) {
            throw new NotUniqueException(element);
        }
        else {
            return new DefaultImmutableSet<T>(elementList.prepend(element));
        }
    }

    /** @return union of this set with set */
    public ImmutableSet<T> union(ImmutableSet<T> set) {
        if (set.isEmpty()) {
            return this;
        }

        ImmutableList<T> unionElements = this.elementList;
        for (T otherEl : set) {
            if (!contains(otherEl)) {
                unionElements = unionElements.prepend(otherEl);
            }
        }
        return new DefaultImmutableSet<T>(unionElements);
    }

    /** @return intersection of this set with set */
    public ImmutableSet<T> intersect(ImmutableSet<T> set) {
        if (set.isEmpty()) {
            return set;
        }

        ImmutableList<T> intersectElements = this.elementList;
        for (T el : intersectElements) {
            if (!set.contains(el)) {
                intersectElements = intersectElements.removeFirst(el);
            }
        }
        return new DefaultImmutableSet<T>(intersectElements);
    }

    /** @return Iterator<T> of the set */
    public Iterator<T> iterator() {
        return elementList.iterator();
    }

    /** @return true iff obj in set */
    public boolean contains(T obj) {
        return elementList.contains(obj);
    }

    /** @return true iff this set is subset of set s */
    public boolean subset(ImmutableSet<T> s) {
        if (size() > s.size()) {
            return false;
        }
        else {
            for (T el : this) {
                if (!s.contains(el)) {
                    return false;
                }
            }
        }
        return true;
    }

    /** @return int the cardinality of the set */
    public int size() {
        return elementList.size();
    }

    /** @return true iff the set is empty */
    public boolean isEmpty() {
        return false;
    }

    public ImmutableSet<T> remove(T element) {
        final ImmutableList<T> list = elementList.removeFirst(element);
        return (ImmutableSet<T>) (list.isEmpty() ? DefaultImmutableSet
                .<T> nil() : new DefaultImmutableSet<T>(list));
    }

    /**
     * @return true iff the this set is subset of o and vice versa.
     */
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (!(obj instanceof ImmutableSet)) {
            return false;
        }
        @SuppressWarnings("unchecked")
        ImmutableSet<T> o = (ImmutableSet<T>) obj;
        return (o.subset(this) && this.subset(o));
    }

    /**
     * Convert the set to a Java array (O(n))
     */
    public <S> S[] toArray(S[] array) {
        return elementList.toArray(array);
    }

    public int hashCode() {
        int hashCode = 0;
        ImmutableList<T> crt = this.elementList;

        while (!crt.isEmpty()) {
            final T element = crt.head();
            hashCode =
                    17 * (element == null ? 0 : element.hashCode()) + hashCode;
            crt = crt.tail();
        }
        return hashCode;
    }

    /**
     * Get the underlying immutable list.
     *
     * @return an immutable list with the same iteration order as this set.
     */
    public ImmutableList<T> toImmutableList() {
        return elementList;
    }

    /**
     * Create an immutable set from an immutable list.
     *
     * @param list
     *            a non-null immutable list
     * @return a fresh immutable set with the same iteration order.
     */
    public static <T> ImmutableSet<T> fromImmutableList(ImmutableList<T> list) {
        return new DefaultImmutableSet<T>(list);
    }

    /**
     * Creates an immutable set from an array list.
     *
     * @param list
     *            a non-null array list.
     * @return a fresh immutable set with the same iteration order.
     */
    public static <T> ImmutableSet<T> fromArrayList(ArrayList<T> list) {
        ImmutableList<T> internalList = ImmutableSLList.nil();
        for (int i = list.size() - 1; i >= 0; i++) {
            internalList = internalList.prepend(list.get(i));
        }

        return new DefaultImmutableSet<T>(internalList);
    }

    /**
     * Creates an immutable set from an iterable.
     *
     * @param list
     *            a non-null iterable.
     * @return a fresh immutable set with the same iteration order.
     */
    public static <T> ImmutableSet<T> fromArrayList(Iterable<T> list) {
        ImmutableList<T> internalList = ImmutableSLList.nil();
        Iterator<T> it = list.iterator();
        while (it.hasNext()) {
            internalList = internalList.append(it.next());
        }

        return new DefaultImmutableSet<T>(internalList);
    }

    public String toString() {
        Iterator<T> it = this.iterator();
        StringBuffer str = new StringBuffer("{");
        while (it.hasNext()) {
            str.append(it.next());
            if (it.hasNext()) {
                str.append(",");
            }
        }
        str.append("}");
        return str.toString();
    }

    /** represents the empty set for elements of type <T> */
    private static class NILSet<T> extends DefaultImmutableSet<T> {

        /**
         * 
         */
        private static final long serialVersionUID = -8055357307337694419L;
        static final NILSet<?> NIL = new NILSet<>();

        private NILSet() {
        }

        /**
         * the NIL list is a singleton. Deserialization builds a new NIL object
         * that has to be replaced by the singleton.
         */
        private Object readResolve() throws java.io.ObjectStreamException {
            return NIL;
        }

        /** adds an element */
        public ImmutableSet<T> add(T element) {
            return new DefaultImmutableSet<T>(element);
        }

        /** adds an element (which is unique, since the set was empty) */
        public ImmutableSet<T> addUnique(T element) {
            return new DefaultImmutableSet<T>(element);
        }

        /** @return union of this set with set */
        public ImmutableSet<T> union(ImmutableSet<T> set) {
            return set;
        }

        /** @return true iff obj in set */
        public boolean contains(T obj) {
            return false;
        }

        /** @return Iterator<T> of the set */
        public Iterator<T> iterator() {
            return ImmutableSLList.<T> nil().iterator();
        }

        /** @return true iff this set is subset of set s */
        public boolean subset(ImmutableSet<T> s) {
            return true;
        }

        /** @return int the cardinality of the set */
        public int size() {
            return 0;
        }

        /** @return true iff the set is empty */
        public boolean isEmpty() {
            return true;
        }

        /**
         * @return true iff the this set is subset of o and vice versa.
         */
        public boolean equals(Object o) {
            return o instanceof NILSet<?>;
        }

        public int hashCode() {
            return 23456;
        }

        public String toString() {
            return "{}";
        }

        public ImmutableSet<T> remove(T element) {
            return this;
        }

        public <S> S[] toArray(S[] array) {
            return array;
        }

    }

}