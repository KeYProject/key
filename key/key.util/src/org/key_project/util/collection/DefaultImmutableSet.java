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

import java.util.Iterator;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;


/**
 * implementation of a persistent set using the SLListOf<T> implementation
 * with all its implications (means e.g. O(n) for adding an
 * element and so on.
 */
public class DefaultImmutableSet<T> implements ImmutableSet<T> {

    /**
     *
     */
    private static final long serialVersionUID = -5000602574000532257L;

    /**
     * Constant defining the set size at which an optimized union operation will be executed.
     */
    public static final int UNION_OPTIMIZATION_SIZE = 100;

    /** list containing the elements */
    private final ImmutableList<T> elementList;

    /** the empty set */
    @SuppressWarnings("unchecked")
   public static final <T> DefaultImmutableSet<T> nil() {
	return (DefaultImmutableSet<T>) NILSet.NIL;
    }


    protected DefaultImmutableSet() {
	elementList = ImmutableSLList.<T>nil();
    }

    /** creates new set with one element
     * @param element of type <T> the new Set contains
     */
    protected DefaultImmutableSet(T element) {
	elementList = (ImmutableList<T>) (ImmutableSLList.<T>nil()).prepend(element);
    }

    /** creates new set containg all elements from the elementList
     * PRECONDITION: elementList has no duplicates
     * @param elementList IList<T> contains all elements of the new Set
     */
    private DefaultImmutableSet(ImmutableList<T> elementList) {
	this.elementList=elementList;
    }


//    private static HashSet<String> previousComplains = new HashSet<>();
    private void complainAboutSize() {
//        // Immutable linear sets are very expensive with O(n) addition
//        // and O(n) lookup.
//        // To create a list with N entries O(N^2) comparisons need to be made
//        // Better restrict this class to very small instances.
//        // The following helps detecting "bad" usages. (MU 2016)
//        if(elementList.size() > 20) {
//            StackTraceElement[] st = new Throwable().getStackTrace();
//            String complain = "TOO LARGE: " + st[2];
//            if(previousComplains.add(complain)) {
//                System.err.println(complain);
////                for (int i = 2; i < 6; i++) {
////                    System.err.println(st[i]);
////                }
//            }
//        }
    }

    /** adds an element
     * @param element of type <T> that has to be added to this set
     */
    public ImmutableSet<T> add(T element) {
        complainAboutSize();
	if (elementList.contains(element)) {
	    return this;
	}
	return new DefaultImmutableSet<T>(elementList.prepend(element));
    }

    /** adds an element, barfs if the element is already present
     * @param element of type <T> that has to be added to this set
     * @throws org.key_project.utils.collection.NotUniqueException if the element is already present
     */
    public ImmutableSet<T> addUnique(T element) throws NotUniqueException {
        complainAboutSize();
	if (elementList.contains(element)) {
	    throw new NotUniqueException(element);
	} else {
	    return new DefaultImmutableSet<T>(elementList.prepend(element));
	}
    }

    /** @return union of this set with set */
    public ImmutableSet<T> union(ImmutableSet<T> set) {
	if(set instanceof DefaultImmutableSet && size() * set.size() > UNION_OPTIMIZATION_SIZE) {
	    return newUnion((DefaultImmutableSet<T>) set);
	}

	return originalUnion(set);
    }


    private DefaultImmutableSet<T> newUnion(DefaultImmutableSet<T> set) {
        ImmutableList<T> otherList = set.elementList;
        ImmutableList<T> clean = Immutables.concatDuplicateFreeLists(this.elementList, otherList);
	    return new DefaultImmutableSet<T>(clean);
    }

    private DefaultImmutableSet<T> originalUnion(ImmutableSet<T> set) {
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
        complainAboutSize();
	if (set.isEmpty()) {
	    return set;
	}
	
	ImmutableList<T> intersectElements = this.elementList;
	for (T el : intersectElements) {	    	    
	    if (!set.contains(el)) {
		intersectElements = intersectElements.removeFirst(el);
	    }
	}
	if(intersectElements.isEmpty()) {
	    return DefaultImmutableSet.<T>nil();
	} else {
	return new DefaultImmutableSet<T>(intersectElements);
    }
    }

    /** @return Iterator<T> of the set */
    public Iterator<T> iterator() {
	return elementList.iterator();
    }
    
    @Override
    public Stream<T> stream() {
        return StreamSupport.stream(spliterator(), false);
    }

    /** @return true iff obj in set */
    public boolean contains(T obj) {
        complainAboutSize();
	return elementList.contains(obj);
    }

    /** @return true iff this set is subset of set s */
    public boolean subset(ImmutableSet<T> s) {	
	if (size() > s.size()) {
	    return false;
	} else {
	    for (T el: this) {
		if (!s.contains(el)) {
		    return false;
		}
	    }
	}
	return true;
    }
    
    /**
     * return true if predicate is fullfilled for at least one element
     * @param predicate the predicate
     * @return true if predicate is fullfilled for at least one element
     */
    public boolean exists(Predicate<T> predicate) {        
        return elementList.exists(predicate);
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
	return (ImmutableSet<T>) (list.isEmpty() ? DefaultImmutableSet.<T>nil() : new DefaultImmutableSet<T>(list));
    }


    /** @return true iff the this set is subset of o and vice versa.
     */
    public boolean equals(Object obj) {
	if (obj==this) {
	    return true;
	}
	if (!(obj instanceof ImmutableSet)) {
	    return false;
	}
	@SuppressWarnings("unchecked")
   ImmutableSet<T> o=(ImmutableSet<T>) obj;
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
            hashCode = (element == null ? 0 : element.hashCode()) + hashCode;
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
    public static<T> ImmutableSet<T> fromImmutableList(ImmutableList<T> list) {
        if(list.isEmpty()) {
            return nil();
        } else {
            return new DefaultImmutableSet<T>(Immutables.removeDuplicates(list));
        }
    }
    
    /**
     * Create an immutable set from a mutable set
     *
     * @param set
     *            a non-null mutable set
     * @return a fresh immutable set with all the elements in set
     */
    public static<T> ImmutableSet<T> fromSet(Set<T> set) {
        if(set.isEmpty()) {
            return nil();
        } else {
            ImmutableList<T> backerList = ImmutableSLList.nil();
            for (T element : set) {
                backerList = backerList.prepend(element);
            }
            return new DefaultImmutableSet<T>(backerList);
        }
    }

    public String toString() {
	Iterator<T> it=this.iterator();
	StringBuffer str=new StringBuffer("{");
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

	private NILSet() {}

	/** the NIL list is a singleton. Deserialization builds
	 * a new NIL object that has to be replaced by the singleton.
	 */
	private Object readResolve()
	throws java.io.ObjectStreamException {
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
	    return ImmutableSLList.<T>nil().iterator();
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

	/** @return true iff the this set is subset of o and vice versa.
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
