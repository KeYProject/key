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

import javax.annotation.Nonnull;

import java.lang.reflect.Array;
import java.util.*;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

public class ImmutableArray<S> implements java.lang.Iterable<S>, java.io.Serializable {

    /**
     *
     */
    private static final long serialVersionUID = -9041545065066866250L;

    private final S[] content;

    /** creates an empty new <S>Array
     */
    @SuppressWarnings("unchecked")
    public ImmutableArray() {
        content = (S[]) new Object[0];
    }

    /** creates a new <S>Array
     * @param arr the ProgrammElement array to wrap
     */
    @SuppressWarnings("unchecked")
    public ImmutableArray(S... arr) {
        content = (S[]) Array.newInstance(arr.getClass().getComponentType(), arr.length);
        System.arraycopy(arr, 0, content, 0, arr.length);
    }


    /** creates a new <S>Array
     * @param list a LinkedList (order is preserved)
     */
    @SuppressWarnings("unchecked")
    public ImmutableArray(List<S> list) {
        content = (S[]) list.toArray();
    }

    /**
     * creates a new immutable array with the contents of the given collection.
     *
     * The order of elements is defined by the collection
     *
     * @param seq non-null
     */
    public ImmutableArray(@Nonnull Collection<S> seq) {
        this(new ArrayList<>(seq));
    }


    /** gets the element at the specified position
     * @param pos an int describing the position
     * @return the element at pos
     */
    public final S get(int pos) {
	return content[pos];
    }

    /**
     * returns the last element of the array
     * @return the element at position size() - 1
     */
    public final S last() {
	return content[content.length - 1];
    }


    /** @return size of the array */
    public int size() {
	return content.length;
    }

    public void arraycopy(int srcIdx, Object dest, int destIndex, int length) {
	System.arraycopy(content, srcIdx, dest, destIndex, length);
    }

    public final boolean isEmpty() {
       return content.length == 0;
    }

    public boolean contains(S op) {
	for (S el : content) {
	   if (el.equals(op)) {
	       return true;
	   }
	}
	return false;
    }

    /**
     * Convert the array to a Java array (O(n))
     * @throws ClassCastException if T is not a supertype of S
     */
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] array) {
	T[] result;
	if (array.length < size()) {
	    result = (T[]) Array.newInstance(array.getClass().getComponentType(), content.length);
	} else {
	    result = array;
	}
	System.arraycopy(content, 0, result, 0, content.length);
	return result;
    }

    @Override
    public int hashCode() {
	return Arrays.hashCode(content);
    }

    @Override
    @SuppressWarnings("unchecked")
    public boolean equals (Object o) {
	if (o == this) {
	    return true;
	}
	S[] cmp = null;
	if (o instanceof ImmutableArray) {
	    cmp = ((ImmutableArray<S>) o).content;
	} else {
		return false;
	}

	if (cmp.length != content.length) {
	    return false;
	}

	for (int i = 0; i < content.length; i++) {
	    if (!content[i].equals(cmp[i])) {
	    	return false;
	    }
	}
	return true;
    }

    @Override
    public String toString() {
	StringBuilder sb = new StringBuilder();
	sb.append("[");
	for (int i = 0, sz = size(); i < sz; i++) {
        sb.append(content[i]);
	    if (i<sz-1) sb.append(",");
	}
	sb.append("]");
	return sb.toString();
    }

    @Override
    public Iterator<S> iterator() {
	return new ArrayIterator<S>(this);
    }

    private static class ArrayIterator<T> implements Iterator<T> {

	private int i = 0;
	private final ImmutableArray<T> coll;

	ArrayIterator(ImmutableArray<T> coll) {
	    this.coll = coll;
	}

	@Override
    public boolean hasNext() {
	    return i < coll.size();
	}

	@Override
    public T next() {
	    return coll.get(i++);
	}

	@Override
    public void remove() {
	    throw new UnsupportedOperationException("Illegal modification access on unmodifiable array.");
	}
    }

    /**
     * Convert an {@link ImmutableArray} to an {@link ImmutableList}.
     *
     * @return This element converted to an {@link ImmutableList}.
     */
    public ImmutableList<S> toImmutableList() {
        ImmutableList<S> ret = ImmutableSLList.<S>nil();
        Iterator<S> it = iterator();
        while (it.hasNext()) {
            ret = ret.prepend(it.next());
        }
        return ret.reverse();
    }

    /**
     * Convert an {@link ImmutableArray} to a {@link List}.
     *
     * @return This element converted to a {@link List}.
     */
    public List<S> toList() {
        List<S> result = new ArrayList<>();
        Iterator<S> it = iterator();
        while (it.hasNext()) {
            result.add(it.next());
        }
        return result;
    }


    /**
     * A stream object for this collection.
     *
     * @return a non-null stream object
     */
    public Stream<S> stream() {
        return StreamSupport.stream(spliterator(), false);
    }
}
