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

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.util.Debug;

/** 
 * this class describes the position of a statement in a program.
 */
public class PosInProgram {
  
    /** pos at the beginning of the program */
    public static final PosInProgram TOP = new PosInProgram();


    private final PosInProgram prev;
    
    /** 
     * the position number
     */
    private final int pos;

    /** 
     * the depth
     */
    private final int depth;

    /**
     * caches iterator for performance reasons
     */
    private int[] cache;

    private final int hashCode;

    /** 
     * returns the ProgramElement at the given position 
     * @param pos the PosInProgram 
     * @param prg the ProgramElement we walk through
     * @return the ProgramElement at the given position 
     * @throws IndexOutOfBoundsException if the given position 
     * refers to a non-existant program 
     */
    public static ProgramElement getProgramAt(PosInProgram pos,
					      ProgramElement prg)
    {
	ProgramElement result = prg;
	final IntIterator it = pos.iterator();	
	while (it.hasNext()) {	
            if(!(result instanceof NonTerminalProgramElement)) {
                throw new IndexOutOfBoundsException("PosInProgram is invalid.");
            }
            // getchild at throws an array index out of bound if 
            // it.next refers to a non-existing child
	    result = 
                ((JavaNonTerminalProgramElement)result).getChildAt(it.next());
	}
	return result;
    }

    /** 
     * creates a new program position
     */
    private PosInProgram(PosInProgram pip, int posNr) {
	prev = pip;
	pos = posNr;
	depth = pip.depth + 1;
	hashCode = prev.hashCode * 31 + pos;
    }   

    /**
     * creates a new PosInProgram 
     * position. 
     */
    private PosInProgram() {
	pos = -1;
	prev = null;
	depth = 0;
	hashCode = 17;
    }   

    /** size of the position list */
    public int depth() {
	return depth;
    }
      
    /** descending downwards choosing the n'th statement of the program 
     * @param n the int describes the position of the statement in the block
     * @return position of the statement
     */    
    public PosInProgram down(int n) {
	return new PosInProgram(this, n);
    }

    /**
     * ascends one AST level 
     *
     */
    public PosInProgram up() {
	return this == TOP ? this : prev;
    }

    public PosInProgram append(PosInProgram pp) {
        return add(this, pp);
    }
    
    public PosInProgram prepend(PosInProgram pp) {
        return add(pp, this);
    }

    private PosInProgram add(PosInProgram first, PosInProgram second) {
        if (first == TOP) {
            return second;
        } else if (second == TOP) {
            return first;
        }        

        PosInProgram result  = first;
        final IntIterator it = second.iterator();
        while (it.hasNext()) {
            result = new PosInProgram(result, it.next());
        }
        return result;
    }

    /** 
     * compares this PosInProgram with another PosInProgram
     * and returns true if both describe the same position 
     */
    public boolean equals(Object obj) {
        if ( this == obj )
            return true;
        
	if (!(obj instanceof PosInProgram)) {
	    return false;
	} 
        
	final PosInProgram cmp = (PosInProgram) obj;

	if (depth != cmp.depth) {
	    return false;
	}

	final IntIterator it = reverseIterator();
	final IntIterator cmpIt = cmp.reverseIterator();
	while (it.hasNext()) {
	    if (it.next() != cmpIt.next()) {
		return false;
	    }
	}
	return true;
    }

    
    public boolean leq(PosInProgram pip) {
	final IntIterator longerIt  = iterator();	
	final IntIterator shorterIt = pip.iterator();
	
	while (shorterIt.hasNext() && longerIt.hasNext()) {
	    if (shorterIt.next() < longerIt.next()) {
		return false;
	    }
	}

	return true;
    }

    /**
     * returns an Iterator<Integer> that iterates through the subterms
     * of a sequent in the reverse order as the PosInProgram has been defined.
     * @return Iterator<Integer> that iterates through the subterms
     * of a sequent in the reverse order as the PosInProgram has been defined.
     */ 
    public IntIterator reverseIterator() {
	return new PosIntIterator(this);
    }


    public int get(int i) {
	if (i >= depth || i < 0) {
	    throw new ArrayIndexOutOfBoundsException();
	}
	if (cache != null) {
	    return cache[i];
	}
	
	PosInProgram previous = this;
	int result = this.pos;

	for (int k = 0; k < depth - i; k++) {	    
	    result = previous.pos;
	    previous = previous.prev;
	}

	return result;
    }

    /**
     * return the last index (or -1 if this == TOP)
     */
    public int last() {
	return pos;
    }

    public ProgramElement getProgram(ProgramElement pe) {
	return getProgramAt(this, pe);
    }

    /**
     * returns an iterator over the list defining the position in a term.
     * @return an iterator over the list defining the position in a term.
     */
    public IntIterator iterator() {	
	if (cache == null) {	
            fillCache();
	} 	
	return new PosArrayIntIterator(cache);
    }
    
  

    private void fillCache() {
	cache = new int[depth];
        if (prev != null &&
                prev.cache != null) {
            System.arraycopy(prev.cache, 0, cache, 0, prev.cache.length);
            cache[cache.length-1] = pos;
        } else {
            final IntIterator it = reverseIterator();
            int at = depth - 1;	    
            while (it.hasNext()) {
                cache[at] = it.next();
                at--;
            }
        }
    }

    
    /** toString */
    public String toString() {
	IntIterator it = iterator();
	String list = "["; 
	while (it.hasNext()) {
	    list += ""+it.next();
	    if (it.hasNext()) {
		list +=", "; 
	    }
	}
	return "PosInProgram: "+list;
    }
    


    static class PosIntIterator implements IntIterator {
	private PosInProgram p;
	
	public PosIntIterator(PosInProgram p) {
	    this.p = p;
	}

	public boolean hasNext() {
	    return p != null && p != TOP;
	}

	public int next() {
	    Debug.assertTrue(p != TOP && p!=null);
	    int result = p.pos; 
	    p = p.prev;
	    return result;
	}
		
    }

    static class PosArrayIntIterator implements IntIterator {
	private final int[] pos;
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