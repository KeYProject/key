
package de.uka.ilkd.key.lang.clang.common.program.statement;

import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.util.Debug;

/** a NON-DESTRUCTIVE single linked list for elements of type IStatement. The
 *    costs of the  
 * different operations are O(1) for prepending one element,
 * O(m) for prepending a list with m elements, 
 * O(n) for appending an element to this list(size n)
 * O(n) for appending a list with m elements to this list (size n)
 * head() has O(1)
 * tail has O(1)
 * size has O(1)
 * ATTENTION appending and prepending and element can be realized 
 * with O(1) costs (see Osaka) then having tail and head with
 * amortized O(1). This will be done later (if necessary).
 */

public abstract class SLListOfIStatement implements ListOfIStatement {
    
    /** the empty list */
    public static final SLListOfIStatement EMPTY_LIST=new NIL();

    /**
     * Reverses this list (O(N))
     */
    public ListOfIStatement reverse() {
	if ( size () <= 1 )
	    return this;

	ListOfIStatement rest = this;
	ListOfIStatement rev  = EMPTY_LIST;
	while (rest != EMPTY_LIST) {
	    rev = rev.prepend(rest.head());
	    rest = rest.tail();
	}
	return rev;
    }


    /**
     * Convert the list to a Java array (O(n))
     */
    public IClangStatement[] toArray() {
	IClangStatement[]     res  = new IClangStatement [ size () ];
	int       i    = 0;
	ListOfIStatement rest = this;
	while ( rest != EMPTY_LIST ) {
	    res[i++] = rest.head ();
	    rest     = rest.tail ();
	}
	return res;
    }


    /** prepends array (O(n))
     * @param array the array of the elements to be prepended
     * @return ListOfIStatement the new list  
     */
    public ListOfIStatement prepend(IClangStatement[] array) {
	return prepend ( array, array.length );
    }


    /** 
     * prepends the first <code>n</code> elements of an array (O(n))
     * @param array the array of the elements to be prepended
     * @param n an int specifying the number of elements to be prepended 
     * @return ListOfIStatement the new list  
     */
    protected ListOfIStatement prepend(IClangStatement[] array, int n) {
	ListOfIStatement res = this;
	while ( n-- != 0 )
	    res = new Cons(array[n], (SLListOfIStatement)res);
	return res;
    }

    /** 
     * first <code>n</code> elements of the list are truncated
     * @param n an int specifying the number of elements to be truncated
     * @return ListOfIStatement this list without the first <code>n</code> elements  
     */
    public ListOfIStatement take(int n) {
	if ( n < 0 || n > size () )
	    throw new IndexOutOfBoundsException
		( "Unable to take " + n + " elements from list " + this );
	
	ListOfIStatement rest = this;

	while ( n-- != 0 )
	    rest = rest.tail ();

	return rest;
    }


    static class Cons extends SLListOfIStatement{
	
	/** the first element */
	private final IClangStatement element;
	/** reference to the next element (equiv.to the tail of list) */ 
	private final SLListOfIStatement cons;
	/** size of the list */
	private final int size;
	/** caches the hashcode */
	private final int hashCode;
	
	/** new list with only one element
	 * @param element the only element in list
	 */
	Cons(IClangStatement element) {
	    this.element=element;
	    cons=EMPTY_LIST;
	    size=1;
	    hashCode=(element == null ? 0 : element.hashCode()); 
	}
	    
	/** constructs a new list with element as head and cons as tail
	 * @param element a IStatement stored in the head element of the list
	 * @param cons tail of the list 
	 */
	Cons(IClangStatement element, SLListOfIStatement cons) {
	    this.element=element;
	    this.cons=cons;
	    size=cons.size()+1;
	    hashCode=(element == null ? 0 : element.hashCode()) + 
		31*cons.hashCode(); 
	}

	/** creates a new list with element as head and the
	 * momentan list as tail (O(1))
	 * @param e the IStatement to be prepended
	 * @return ListOfIStatement the new list  
	 */
	public ListOfIStatement prepend(IClangStatement e) {
	    return new Cons(e, this);
	}
	
	/** prepends list (O(n))
	 * @param list the ListOfIStatement to be prepended
	 * @return ListOfIStatement the new list  
	 */
	public ListOfIStatement prepend(ListOfIStatement list) {
	    return prepend ( list.toArray () );
	}

	/** appends element at end (non-destructive) (O(n))
	 * @param e the IStatement to be prepended
	 * @return ListOfIStatement the new list  
	 */
	public ListOfIStatement append(IClangStatement e) {
	    return (new Cons(e)).prepend(this);
	}

	/** appends element at end (non-destructive) (O(n))
	 * @param list the ListOfIStatement to be appended
	 * @return ListOfIStatement the new list  
	 */    
	public ListOfIStatement append(ListOfIStatement list) {
	    return list.prepend(this);
	}

	/** appends element at end (non-destructive) (O(n))
	 * @param array the array to be appended
	 * @return ListOfIStatement the new list  
	 */    
	public ListOfIStatement append(IClangStatement[] array) {
	    return EMPTY_LIST.prepend ( array ).prepend ( this );
	}

	/** @return IStatement first element in list */
	public IClangStatement head() {
	    return element;
	}
	
	/** @return ListOfIStatement tail of the list */
	public ListOfIStatement tail() {
	    return cons;
	}
	
	/**
	 * hashcode for collections, implemented same algorithm as
         * java.util.Collections use 	 
	 * @return the hashcode of the list
         */
	public int hashCode() {
	    return hashCode;
	}

	
	/** @return iterator through list */
	public IteratorOfIStatement iterator() {
	    return new SLListIterator(this);
	}
	
	/** @return int the number of elements in list */    
	public int size() {
	    return size;
	}

	/** @return boolean true iff. obj in list */
	public boolean contains(IClangStatement obj) {
	    ListOfIStatement list = this;
	    IClangStatement       t;
	    while (list != EMPTY_LIST) {
		t = list.head ();
		if ( t == null ? obj == null : t.equals ( obj ) )
		    return true;
		list = list.tail();
	    }
	    return false;
	}

	/** @return true iff the list is empty */
	public boolean isEmpty() {
	    return false;
	}


	/** removes first occurrences of obj (O(n))
	 * @return new list 
	 */
	public ListOfIStatement removeFirst(IClangStatement obj) {
	    IClangStatement[]       res            = new IClangStatement [ size () ];
	    int         i              = 0;
	    SLListOfIStatement rest           = this;
	    SLListOfIStatement unmodifiedTail = this;
	    IClangStatement         t;
	    while (rest != EMPTY_LIST) {
		t    = rest.head ();
		rest = (SLListOfIStatement)rest.tail();
		if ( !( t == null ? obj == null : t.equals ( obj ) ) )
		    res[i++] = t;
		else {
		    unmodifiedTail = rest;
		    return unmodifiedTail.prepend( res, i );
		}
	    }
	    return this;
	    
	}
	

	/** 
	 * removes all occurrences of obj (O(n))
	 * @return new list 
	 */
	public ListOfIStatement removeAll(IClangStatement obj) {
	    IClangStatement[]       res            = new IClangStatement [ size () ];
	    int         i              = 0;
	    SLListOfIStatement rest           = this;
	    SLListOfIStatement unmodifiedTail = this;
	    IClangStatement         t;

	    while (rest != EMPTY_LIST) {
		t    = rest.head ();
		rest = (SLListOfIStatement)rest.tail();
		if ( !( t == null ? obj == null : t.equals ( obj ) ) )
		    res[i++] = t;
		else
		    unmodifiedTail = rest;
	    }

	    return unmodifiedTail.prepend
		( res, i - unmodifiedTail.size () );
	}


	public boolean equals(Object o) {
	    if ( ! ( o instanceof ListOfIStatement ) ) 
		return false;
	    ListOfIStatement o1 = (ListOfIStatement) o;
	    if ( o1.size() != size() ) 
		return false;
	    IteratorOfIStatement p = iterator();
		IteratorOfIStatement q = (o1).iterator();
	    while ( p.hasNext() ) {
	        IClangStatement ep = p.next();
	        IClangStatement eq = q.next();
	        if ( ( ep == null && eq != null ) 
		    || ( ep != null && !ep.equals(eq) ) ) 
		  return false;
	    }
	    return true;
        }


	public String toString() {
	    IteratorOfIStatement it=this.iterator();
	    StringBuffer str=new StringBuffer("[");
	    while (it.hasNext()) {
		str.append(""+it.next());
		if (it.hasNext()) {
		    str.append(",");
		}
	    }	
	    str.append("]");
	    return str.toString();
	}

	/** iterates through a none destructive list */
	private static class SLListIterator implements IteratorOfIStatement {
	
	    /** the list of remaining elements */
	    private ListOfIStatement list;
	
	    /** constructs the iterator
	     *@param list the ListOfIStatement that has to be iterated 
	     */
	    public SLListIterator(ListOfIStatement list) {
		this.list = list;	
	    }
	
	    /** @return next element in list */
	    public IClangStatement next() {
		IClangStatement element = list.head();
		list = list.tail();
		return element;
	    }
	
	    /** @return true iff there are unseen elements in the list
	     */ 
	    public boolean hasNext() {
		return list != EMPTY_LIST;
	    }    
	}


    }


    static class NIL extends SLListOfIStatement{

	private static final SLNilListIterator iterator = 
	    new SLNilListIterator();
	
	NIL() {
	}
    
	/** the NIL list is a singleton. Deserialization builds
	 * a new NIL object that has to be replaced by the singleton.
         */ 
        private Object readResolve() 
            throws java.io.ObjectStreamException {
            return SLListOfIStatement.EMPTY_LIST;
	}
	
	public int size() {
	    return 0;
	}

	public boolean equals ( Object o ) {
	    return o instanceof NIL;
	}
	
	public int hashCode() {
	    return 0;
	}
	
	public ListOfIStatement prepend(IClangStatement element) {
	    return new Cons(element);
	}
	    
	public ListOfIStatement prepend(ListOfIStatement list) {
	    return list;
	}
	    
	public ListOfIStatement append(IClangStatement element) {
	    return new Cons(element);
	}
	    
	public ListOfIStatement append(ListOfIStatement list) {
	    return list;
	}

	public ListOfIStatement append(IClangStatement[] array) {
	    return EMPTY_LIST.prepend ( array );
	}
	    
	public boolean contains(IClangStatement obj) {
	    return false;
	}

	public boolean isEmpty() {
	    return true;
	}
	    
	public IteratorOfIStatement iterator() {
	    return iterator;
	}
	    
	public IClangStatement head() {
	    return null;
	}
	    
	public ListOfIStatement tail() {
	    return this;
	}

	public ListOfIStatement removeAll(IClangStatement obj) {
	    return this;	
	}

	public ListOfIStatement removeFirst(IClangStatement obj) {
	    return this;	
	}
	    
	public String toString() {
	    return "[]";
	}

	/** iterates through the a none destructive NIL list */
	private static class SLNilListIterator implements IteratorOfIStatement {
	    	
	    /** 
	     * creates the NIL list iterator
	     */
	    public SLNilListIterator() {
	    }
	    
	    /** @return next element in list */
	    public IClangStatement next() {
		return null;
	    }

	    /** 
	     * @return true iff there are unseen elements in the list
	     */ 
	    public boolean hasNext() {
		return false;
	    }    
	}
    }
}

    
