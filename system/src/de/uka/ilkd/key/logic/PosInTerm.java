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


/** this class describes a position in a term 
 */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.util.Debug;


public class PosInTerm {
  
    /** top level term position */
    public static final PosInTerm TOP_LEVEL = new PosInTerm();

    private final PosInTerm prev;
    
    /** 
     * the position number
     */
    private final int pos;

    // saves 8 bytes (due to alignment issues) per instance if we use a 
    // short here instead of an int
    /** 
     * the depth
     */
    private final short depth;
    
    // saves 8 bytes (due to alignment issues) per instance if we use a 
    // short here instead of an int
    private final short hashCode;

    /**
     * iterator cache
     */
    private int[] cache;

    private PosInTerm(PosInTerm pit, int posNr) {
	prev = pit;
	pos = posNr;

        if (pit.depth == Short.MAX_VALUE) {
	    throw new IllegalStateException("Overflow detected for field depth in PosInTerm.");
	}
	depth = (short) (pit.depth + 1);
	
	hashCode = (short) (prev.hashCode * 13 + pos);
    }   

    /**
     * creates a new PosInTerm 
     * position. 
     */
    private PosInTerm() {
	pos = -1;
	prev = null;
	depth = 0;
	hashCode = 13;
    }   

    /** size of the position list */
    public int depth() {
	return depth;
    }

  
    /** descending downwards choosing the n'th subterm, subformula 
     * @param n int describs the chosen subterm 
     * @return Position like old Position but with a deeper
     * subterm.
     */
    public PosInTerm down(int n) {
	return new PosInTerm(this, n);
    }
    
    public PosInTerm up() {
       return prev;
    }

    /**
     * @return the number/index of the deepest subterm that this
     *         <code>PosInTerm</code> points to. If the position is top-level,
     *         the result will be <code>-1</code>
     */
    public int getIndex () {
        return pos;
    }
    

    /** 
     * compares this PosInTerm with another PosInTerm
     * and returns true if both describe the same position 
     */
    public boolean equals(Object obj) {
        if ( this == obj )
            return true;
        
	if (!(obj instanceof PosInTerm)) {
	    return false;
	} 

	PosInTerm cmp = (PosInTerm) obj;

	if (depth != cmp.depth) {
	    return false;
	}
		
	PosInTerm thisPIT = this;
    
	while ( thisPIT != TOP_LEVEL ) {
	    if ( thisPIT.pos != cmp.pos )
	        return false;
	    thisPIT = thisPIT.prev;
	    cmp     = cmp.prev;
	    if ( thisPIT == cmp )
	        return true;
	}
    
	return true;
    }

    /**
     * get subterm/-formula information.  A PosInTerm defining the xn'th
     * subterm of the x(n-1)'th subterm of ... of the x1'th subterm of a
     * term returns an iterator subsequently resulting in the list xn...x1.
     * @return Iterator<Integer> that iterates through the subterms
     * of a sequent in the reverse order as the PosInTerm has been defined.
     */ 
    public IntIterator reverseIterator() {
	return new PosIntIterator(this);
    }


    /**
     * returns an iterator defining the position in a term according to
     * subterm relation. A PosInTerm defining the xn'th subterm of the
     * x(n-1)'th subterm of ... of the x1'th subterm of a term returns an
     * iterator subsequently resulting in the list x1...xn.
     * @return an iterator over the list defining the position in a term.
     */
    public IntIterator iterator() {	
	if (cache == null) fillCache();
	return new PosArrayIntIterator(cache);
    }

    private void fillCache() {
	cache = new int[depth];

	IntIterator it = reverseIterator();
	int at = depth - 1;

	while (it.hasNext()) {
	    cache[at] = it.next();
	    at--;
	}
    }

    
    public static PosInTerm parseReverseString(String s) {
	PosInTerm result = TOP_LEVEL;
	if ("".equals(s)) {
	    return result;
	}
	ImmutableList<Integer> list = ImmutableSLList.<Integer>nil();
	java.util.StringTokenizer tker = 
	    new java.util.StringTokenizer(s, ",", false);
	while (tker.hasMoreTokens()) 
	    list = list.prepend(Integer.decode(tker.nextToken()));

        for (Integer aList : list) {
            result = new PosInTerm(result, aList.intValue());
        }

	return result;       
    }

    

    public String integerList(IntIterator it) {
	String list = "["; 
	while (it.hasNext()) {
	    list += ""+it.next();
	    if (it.hasNext()) {
		list +=","; 
	    }
	}
	list += "]";
	return list;
    }

    public String toString() {
	if (this==TOP_LEVEL) {
	    return "top level";
	}

	return "subterm: " + integerList(iterator());
    }



    private static class PosIntIterator implements IntIterator {
	private PosInTerm p;
	
	public PosIntIterator(PosInTerm p) {
	    this.p = p;
	}

	public boolean hasNext() {
	    return p != null && p != TOP_LEVEL;
	}

	public int next() {
	    Debug.assertTrue(p != TOP_LEVEL && p!=null);
	    int result = p.pos; 
	    p = p.prev;
	    return result;
	}	
    }

    private static class PosArrayIntIterator implements IntIterator {
	private int[] pos;
	private int next;

	public PosArrayIntIterator(int[] pos) {
	    this.pos = pos;
	    next = 0;
	    
	}

	public boolean hasNext() {
	    return next < pos.length;
	}

	public int next() {
	    next++;
	    return pos[next-1];
	}		
    }

    
    public int hashCode () {
        return hashCode;
    }
}
