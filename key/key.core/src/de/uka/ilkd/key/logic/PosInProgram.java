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

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;

/** 
 * this class describes the position of a statement in a program.
 */
public class PosInProgram {
  
    /** pos at the beginning of the program */
    public static final PosInProgram TOP = new PosInProgram();

    /** often used positions */
    public static final PosInProgram ZERO = TOP.down(0);
    public static final PosInProgram ZERO_ZERO = ZERO.down(0);
    public static final PosInProgram ZERO_ONE  = ZERO.down(1);
    public static final PosInProgram ONE = TOP.down(1);
    public static final PosInProgram ONE_ZERO = ONE.down(0);
    public static final PosInProgram ONE_ONE  = ONE.down(1);


    /** 
     * the position number
     */
    private final int[] pos;
    
    /**
     * pointer to the (last element + 1) in pos valid for this position
     */
    private final int depth;

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
        for (int i = 0; i<pos.depth; i++) {
            if(!(result instanceof NonTerminalProgramElement)) {
                throw new IndexOutOfBoundsException("PosInProgram is invalid.");
            }
            // getchild at throws an array index out of bound if 
            // it.next refers to a non-existing child
            result = ((NonTerminalProgramElement)result).getChildAt(pos.pos[i]);
        }

        return result;
    }

    /** 
     * creates a new program position
     */
    private PosInProgram(PosInProgram pip, int posNr) {
        pos = new int[pip.depth + 1]; 
        System.arraycopy(pip.pos, 0, pos, 0, pip.depth);
        pos[pos.length - 1] = posNr;
        depth = pos.length;
    }   

    /**
     * creates a new PosInProgram 
     * position. 
     */
    private PosInProgram() {
	pos = new int[0];
	depth = 0;
    }   

    private PosInProgram(int[] pos, int depth) {
        this.pos = pos;
        this.depth = depth; 
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
        final PosInProgram up;
        if (this != TOP) {
            up = new PosInProgram(this.pos, depth - 1); 
        } else {
            up = TOP;
        }
        return up;
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

        if (obj == null || this.getClass() != obj.getClass()) {
            return false;
        } 

        final PosInProgram cmp = (PosInProgram) obj;

        if (depth != cmp.depth) {
            return false;
        }

        for (int i = 0; i<depth; i++) {
            if (cmp.pos[i] != pos[i]) {
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

    public int get(int i) {
        if (i >= depth || i < 0) {
            throw new ArrayIndexOutOfBoundsException();
        }
        return pos[i];
    }

    /**
     * return the last index (or -1 if this == TOP)
     */
    public int last() {
	return pos[depth-1];
    }

    public ProgramElement getProgram(ProgramElement pe) {
	return getProgramAt(this, pe);
    }

    /**
     * returns an iterator over the list defining the position in a term.
     * @return an iterator over the list defining the position in a term.
     */
    public IntIterator iterator() {	
        return new PosArrayIntIterator(this);
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
    


    static class PosArrayIntIterator implements IntIterator {
	private final PosInProgram pip;
	private int next;

	public PosArrayIntIterator(PosInProgram pip) {
        this.pip = pip;
	    next = 0;
	}

	public boolean hasNext() {
	    return next < pip.depth;
	}

	public int next() {
	    return pip.pos[next++];
	}
		
    }

    public int hashCode () {
        int hashCode = 0;
        for (int i : pos) {
          hashCode = 31*hashCode + i;
        }
        return hashCode;
    }
}