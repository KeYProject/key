package de.uka.ilkd.key.collection;

import java.lang.reflect.Array;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.util.NotSupported;

public class ImmutableArray<S> implements java.lang.Iterable<S>, java.io.Serializable {

    /**
     *
     */
    private static final long serialVersionUID = -9041545065066866250L;

    private final S[] content;

    private int hashCode = -1;

    /** creates an empty new <S>Array
     */
    public ImmutableArray() {
	content = (S[]) new Object[0];
    }

    /** creates a new <S>Array
     * @param arr the ProgrammElement array to wrap
     */
    public ImmutableArray(S... arr) {
	content = (S[]) Array.newInstance(arr.getClass().getComponentType(), arr.length);
	System.arraycopy(arr, 0, content, 0, arr.length);
    }


    /** creates a new <S>Array
     * @param list a LinkedList (order is preserved)
     */
    public ImmutableArray(List<S> list) {
	content = (S[]) list.toArray();
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

    public boolean contains(S op) {
	for (S el : content) {
	   if (el.equals(op)) {
	       return true;
	   }
	}
	return false;
    }

    public int hashCode() {
	if (hashCode == -1) {
	    for(int i = 0; i < content.length; i++) {
		hashCode += 17 * content[i].hashCode();
	    }
	    if(hashCode == -1) {
		hashCode = -2;
	    }
	}
	return hashCode;
    }

    public boolean equals (Object o) {
	if (o == this) {
	    return true;
	}

	if (!(o instanceof ImmutableArray)) {
	    return false;
	}

	final S[] cmp = ((ImmutableArray<S>) o).content;

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

    public String toString() {
	StringBuilder sb = new StringBuilder();
	sb.append("[");
	for (int i = 0, sz = size(); i < sz; i++) {
	    sb.append(""+content[i]);
	    if (i<sz-1) sb.append(",");
	}
	sb.append("]");
	return sb.toString();
    }

    public Iterator<S> iterator() {
	return new ArrayIterator<S>(this);
    }

    private static class ArrayIterator<T> implements Iterator<T> {

	private int i = 0;
	private final ImmutableArray<T> coll;

	ArrayIterator(ImmutableArray<T> coll) {
	    this.coll = coll;
	}

	public boolean hasNext() {
	    return i < coll.size();
	}

	public T next() {
	    return coll.get(i++);
	}

	public void remove() {
	    throw new NotSupported("Illegal modification access on unmodifiable array.");
	}



    }



}
