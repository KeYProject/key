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
import java.util.Stack;

import de.uka.ilkd.key.util.Debug;

/**
 * This class implements the leftist heap, see &quot;Functional Data
 * Structures&quot; by Chris Okasaki
 */
public abstract class ImmutableLeftistHeap<T extends Comparable<T>> implements ImmutableHeap<T> {

    /**
     *
     */
    private static final long serialVersionUID = -4035441830559680469L;

    

    public static <T extends Comparable<T>> ImmutableLeftistHeap<T> nilHeap() {
	return (ImmutableLeftistHeap<T>) Empty.EMPTY_HEAP;
    }


    /**
     * Length of the right spine, i.e. the length of the path from the
     * root to rightmost leaf
     */
    protected abstract int getRightHeight ();

    /**
     * Class for non-empty heaps
     */
    private static class Node<S extends Comparable<S>> extends ImmutableLeftistHeap<S> {

	/**
         * 
         */
        private static final long serialVersionUID = 4913355498617409303L;

    /**
	 * Length of the right spine, i.e. the length of the path from the
	 * root to rightmost leaf
	 */
	private final int rightHeight;

	private final int size;

	private final S data;

	/**
	 * Children of the root of this heap
	 */
	private final ImmutableLeftistHeap<S> left;
	private final ImmutableLeftistHeap<S> right;


	/**
	 * Node constructor for nodes with only empty children
	 */
	public Node(S element) {	    
	    this.rightHeight = 1;
	    this.size = 1;
	    this.data = element;
	    this.left = ImmutableLeftistHeap.<S>nilHeap();
	    this.right = ImmutableLeftistHeap.<S>nilHeap();
	}

	/**
	 * Node constructor for nodes with at most one non-empty child
	 */
	public Node(S element, ImmutableLeftistHeap<S> a) {
	    this.rightHeight = 1;
	    this.size = 1 + a.size();
	    this.data = element;
	    this.left = a;
	    this.right = ImmutableLeftistHeap.<S>nilHeap();
	}

	/**
	 * Node constructor for nodes
	 */
	private Node(S element,
		     ImmutableLeftistHeap<S> a,
		     ImmutableLeftistHeap<S> b) {
	    data = element;
	    size = 1 + a.size() + b.size();
	    if (a.getRightHeight() <= b.getRightHeight()) {
		rightHeight = a.getRightHeight() + 1;
		left = b;
		right = a;
	    } else {
		rightHeight = b.getRightHeight() + 1;
		left = a;
		right = b;
	    }
	}

	/**
	 * Length of the right spine, i.e. the length of the path from the
	 * root to rightmost leaf
	 */
	protected int getRightHeight () {
	    return rightHeight;
	}

	/**
	 * @return true iff this heap is empty
	 */
	public boolean isEmpty ()
	{
	    return false;
	}

	/**
	 * Add an element to this heap object
	 * @param element the element to be added
	 * @return a heap that contains all elements of this heap, and
	 * additionally <code>element</code>
	 */
	public ImmutableHeap<S> insert ( S element ) {
	    if (element.compareTo(data) <= 0) {
		return new Node<S>(element, this);
	    } else {
		return new Node<S>(data,
                left,
				(ImmutableLeftistHeap<S>)right.insert(element));
	    }
	}

	/**
	 * Add multiple elements to this heap object
	 * @param h a heap containing the elements to be added
	 * @return a heap that contains all elements of this heap, and
	 * additionally all objects from <code>h</code>
	 */
	public ImmutableHeap<S> insert ( ImmutableHeap<S> h ) {
	    if (h.isEmpty()) {
		return this;
	    } else if (h instanceof Node/*<S>*/) {
		Node<S> other = (Node<S>) h;
		if (data.compareTo(other.data) <= 0) {
		    return new Node<S>(data,
                    left,
                                    (ImmutableLeftistHeap<S>)right.insert(other));
		} else {
		    return new Node<S>(other.data,
                    other.left,
			            (ImmutableLeftistHeap<S>)insert(other.right));
		}
	    } else {
		return insert(h.iterator());
	    }
	}

	/**
	 * @return the minimum element of this heap, or null iff this heap
	 * is empty (<code>isEmpty()==true</code>)
	 */
	public S findMin () {
	    return data;
	}

	/**
	 * Remove the minimum element from this heap
	 * @return a heap that contains all elements of this heap except
	 * for the minimum element
	 */
	public ImmutableHeap<S> deleteMin () {
	    return left.insert(right);
	}

	/**
	 * Remove all elements of this heap which are <code>equal</code>
	 * to <code>element</code>.
	 * @return heap that has all occurrences of <code>element</code>
	 * removed
	 */
	public ImmutableHeap<S> removeAll ( S element ) {
	    int c = data.compareTo ( element );

	    if ( c > 0 )
		return this;

	    ImmutableLeftistHeap<S> newLeft  =
		(ImmutableLeftistHeap<S>)left .removeAll ( element );
	    ImmutableLeftistHeap<S> newRight =
		(ImmutableLeftistHeap<S>)right.removeAll ( element );

	    if ( c == 0 && data.equals ( element ) )
		return newLeft.insert ( newRight );
	    if ( left == newLeft && right == newRight )
		return this;
	    return new Node<S> ( data, newLeft, newRight );
	}

	/**
	 * @return the number of elements this heap holds
	 */
	public int size () {
	    return size;
	}

    }

    /**
     * Singleton class for empty heaps
     */
    private static class Empty<S extends Comparable<S>> extends ImmutableLeftistHeap<S> {

	/**
	 *
	 */
	private static final long serialVersionUID = -2471143956420721016L;

	/**
	 * Use this element to construct new heaps
	 */
	private static final ImmutableLeftistHeap<?> EMPTY_HEAP = new Empty();
	
	/**
	 * Length of the right spine, i.e. the length of the path from the
	 * root to rightmost leaf
	 */
	protected int getRightHeight () {
	    return 0;
	}

	/**
	 * @return true iff this heap is empty
	 */
	public boolean isEmpty () {
	    return true;
	}

	/**
	 * Add an element to this heap object
	 * @param element The element to be added
	 * @return a heap that contains all elements of this heap, and
	 * additionally <code>element</code>
	 */
	public ImmutableHeap<S> insert ( S element ) {
	    return new Node<S> (element);
	}

	/**
	 * Add multiple elements to this heap object
	 * @param h a heap containing the elements to be added
	 * @return a heap that contains all elements of this heap, and
	 * additionally all objects from <code>h</code>
	 */
	public ImmutableHeap<S> insert ( ImmutableHeap<S> h ) {
	    return h;
	}

	/**
	 * @return the minimum element of this heap, or null iff this heap
	 * is empty (<code>isEmpty()==true</code>)
	 */
	public S findMin () {
	    return null;
	}

	/**
	 * Remove the minimum element from this heap
	 * @return a heap that contains all elements of this heap except
	 * for the minimum element
	 */
	public ImmutableHeap<S> deleteMin () {
	    return this;
	}

	/**
	 * Remove all elements of this heap which are <code>equal</code>
	 * to <code>element</code>.
	 * @return heap that has all occurrences of <code>element</code>
	 * removed
	 */
	public ImmutableHeap<S> removeAll ( S element ) {
	    return this;
	}

	/**
	 * @return the number of elements this heap holds
	 */
	public int size () {
	    return 0;
	}

    }

    /**
     * Add multiple elements to this heap object
     * @param elements the elements to be added
     * @return a heap that contains all elements of this heap, and
     * additionally all objects from <code>elements</code>
     */
    public ImmutableHeap<T> insert ( Iterator<T> elements ) {
	// Use bottom-up strategy to compose new heap in O(n)

	Stack<ImmutableHeap<T>> s = new Stack<ImmutableHeap<T>>();
	s.push(this);
	while (elements.hasNext()) {
	    ImmutableHeap<T> h = new Node<T>(elements.next());
	    do {
		ImmutableHeap<T> top = s.peek();
		if (h.size() >= top.size()) {
		    h = h.insert(top);
		    s.pop();
		} else {
		    break;
		}
	    } while (!s.isEmpty());
	    s.push(h);
	}
	ImmutableHeap<T> res = s.pop();
	while (!s.isEmpty()) {
	    res = res.insert(s.pop());
	}
	return res;
    }

    /**
     * @return an iterator that returns all elements of this heap
     */
    public Iterator<T> iterator () {
	return new UnsortedIterator<T> ( this );
    }

    /**
     * @return an iterator that returns all elements of this heap in
     * increasing order
     */
    public Iterator<T> sortedIterator () {
	return new SortedIterator<T> ( this );
    }


    public String toString() {
	Iterator<T> it=this.iterator();
	StringBuffer str=new StringBuffer("[");
	while (it.hasNext()) {
	    str.append(it.next());
	    if (it.hasNext()) {
		str.append(",");
	    }
	}
	str.append("]");
	return str.toString();
    }


    /**
     * Class for iterating the elements of a heap in unspecified order
     */
    private static class UnsortedIterator<T extends Comparable<T>> implements Iterator<T> {

	private final Stack<Node<T>> remainder = new Stack<Node<T>> ();

	public UnsortedIterator ( ImmutableLeftistHeap<T> heap ) {
	    push ( heap );
	}

	private void push ( ImmutableLeftistHeap<T> heap ) {
	    if ( !heap.isEmpty () )
		remainder.push ( (Node<T>) heap );
	}

	public boolean hasNext () {
	    return !remainder.isEmpty ();
	}

	public T next () {
	    Debug.assertFalse ( remainder.isEmpty (),
				"Missing next element in " +
				"UnsortedIterator.next()" );

	    Node<T> heap = remainder.pop ();
	    // descend in right-first order, this helps to keep the stack small
	    push ( heap.left );
	    push ( heap.right );

	    return heap.data;
	}

	/**
	 * throw an unsupported operation exception as leftiest heaps are immutable
	 */
	public void remove() {
            throw new UnsupportedOperationException();
        }
    }


    /**
     * Class for iterating the elements of a heap in increasing order
     */
    private static class SortedIterator<T extends Comparable<T>> implements Iterator<T> {

	private ImmutableHeap<T> remainder;

	public SortedIterator ( ImmutableHeap<T> heap ) {
	    remainder = heap;
	}

	public boolean hasNext () {
	    return !remainder.isEmpty ();
	}

	public T next () {
	    Debug.assertFalse ( remainder.isEmpty (),
				"Missing next element in " +
				"UnsortedIterator.next()" );

	    T data = remainder.findMin ();
	    remainder = remainder.deleteMin ();

	    return data;
	}

	/**
	 * throw an unsupported operation exception as leftiest heaps are immutable
	 */
	public void remove() {
            throw new UnsupportedOperationException();
        }
    }

}
