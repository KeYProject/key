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

import java.util.LinkedList;
import java.util.StringTokenizer;

/**
 * Describes the position within a term by a sequence of integers.
 * 
 * To create a position  
 * <ul>
 * <li>obtain the position object representing the top level position, which refers to
 *  the term as a whole.</li>
 * <li>use method {@link #down(int)} to keep track of the current position. Pass as argument the
 * position of the subterm to be taken. Attention: Each invocation creates a new position in term
 * object which has to be used for further navigation. The original one remains unchanged.</li>
 * </ul>
 * 
 */
public final class PosInTerm {

    private static final PosInTerm TOP_LEVEL = new PosInTerm();

    // to save memory, we use 16bit integers (unsigned) instead of 32bit
    private final char[] positions;
    private final char size;
    private char hash = (char)-1;
    private boolean copy;

    
    /** 
     * create a position from the string
     * 
     * The string contains a comma separated list of integers.
     * The position created from the string encapsulated the given list but in 
     * reverse order
     * 
     * @param s the String with the list of integers to be interpreted as term indices in 
     * reverse order
     * @return the PosInTerm encapsulating the integer list in reverse order
     */
    public static PosInTerm parseReverseString(String s) {
        if ("".equals(s)) {
            return getTopLevel();
        }
        
        final LinkedList<Integer> list = new LinkedList<Integer>();        
        final StringTokenizer tker = new StringTokenizer(s,",",false);
        
        while (tker.hasMoreTokens()) {
            list.addFirst(Integer.decode(tker.nextToken()));
        }
        
        final char[] positions = new char[list.size()];
        int i = 0;
        for (int j : list) {
            if (j > Character.MAX_VALUE) throw new ArithmeticException("Position "+j+" out of bounds");
            positions[i] = (char)j;
            ++i;
        }
               
        return positions.length == 0 ? getTopLevel() : new PosInTerm(positions, (char) positions.length, true);
    }

    /**
     * returns the instance representing the top level position
     * @return the top level position
     */
    public static PosInTerm getTopLevel() {
        return TOP_LEVEL;
    }
    
    /**
     * only used once to create the singleton for the top level position
     */
    private PosInTerm() {
        positions = new char[0];
        size = 0;
        hash = 13;
        copy = true;
    }

    /**
     * creates an instance representing the position <code>positions[0..size-1]</code>
     * @param positions the integer array where each element describes the position to be taken (in top-to-bottom order)
     * @param size the size of the integer list (attention: might be shorter than the length of the position array)
     * @param copy indicates (i.e. true) if the position array has to be copied when going downwards
     */
    private PosInTerm(char[] positions, char size, boolean copy) {
        assert size > 0 && size <= positions.length;
        this.positions = positions;
        this.size = size;
        this.copy = (copy || (size == positions.length));
    }

    /**
     * the depth of the sub term described by this position
     * @return the term depth
     */
    public int depth() {
        return size;
    }

    /**
     * true if the position describes the top level position, i.e., the term as a whole
     * @return true iff top level
     */
    public boolean isTopLevel() {
        return size == 0;
    }

    /**
     * returns the position of the enclosing term
     * @return the position of the parent
     */
    public PosInTerm up() {
        if (size == 0) {
            return null;
        }
        return size == 1 ? getTopLevel() : new PosInTerm(positions, (char)(size - 1), true);
    }

    /**
     * returns the position of the <code>depth-n</code> parent term
     * @param n the integer specifying the length of the prefix 
     * @return the prefix of this position of length <code>n</code>
     * @throws IndexOutOfBoundsException if <code>n</code> is greater than the depth of this position
     */
    public PosInTerm firstN(int n) {
        if (n > size) {
            throw new IndexOutOfBoundsException("Position is shorter than " + n);
        } else if (n == 0) {
            return getTopLevel();
        } else if (n == size) {
            return this;
        }
        return new PosInTerm(positions, (char)n, true);
    }
    
    /**
     * returns the position for the <code>i</code>-th subterm of the subterm described by this position  
     * @param i the index of the subterm
     * @return the position of the i-th subterm
     */
    public PosInTerm down(int i) {
        if (i > Character.MAX_VALUE) throw new ArithmeticException("Position "+i+" out of bounds");
        
        final PosInTerm result; 
        synchronized(positions) { 
            if (copy) {        
                final char[] newPositions = 
                        new char[positions.length <= size ? size + 4 : positions.length];
                System.arraycopy(positions, 0, newPositions, 0, size);
                newPositions[size] = (char)i;
                result = new PosInTerm(newPositions, (char)(size + 1), false);
            } else {
                positions[size] = (char)i;
                copy   = true;
                result = new PosInTerm(positions, (char)(size + 1), true);            
            }
        }
        return result;
    }

    /**
     * returns the index of the subterm at depth <code>i</code>  
     * @param i the depth of the subterm whose index it to be returned
     * @return an int such that <code>term.subAt(this).sub(getIndex(i)) == term.subAt(firstN(i+1))</code>
     */
    public int getIndexAt(int i) {
        if (i<0 || i>=size) {
            throw new IndexOutOfBoundsException("No position at index "+i);
        }
        return positions[i];
    }

    /** 
     * equivalent to <code>getIndexAt(depth() - 1)</code>
     * @return the index of the subterm described by this position
     */
    public int getIndex() {
        return size == 0 ? -1 : positions[size - 1];
    }

    public int hashCode() {        
        if (hash == (char)-1) {
            hash = 13;
            for (int i = 0; i < size; i++) {
                hash = (char) (13 * hash + positions[i]);
            }        
            hash = hash == -1 ? 0 : hash;
        } 
        return hash;
    }

    public boolean equals(Object o) {
        if (o == this)
            return true;

        if (o != null && o.getClass() == this.getClass()) {
            final PosInTerm p = (PosInTerm) o;

            if (size == p.size) {
                if (positions != p.positions) {
                    for (int i = 0; i < size; i++) {
                        if (positions[i] != p.positions[i]) {
                            return false;
                        }
                    }
                }
                return true;
            }
        }
        return false;
    }

    /**
     * returns a comma separated list of integers enclosed in brackets (the list contains all integers
     * in the order as returned by the iterator)  
     * @param it the iterator
     * @return the String with the list of integers
     */
    public String integerList(IntIterator it) {
        StringBuffer list = new StringBuffer("[");
        while (it.hasNext()) {
            list.append(it.next());
            if (it.hasNext()) {
                list.append(",");
            }
        }
        list.append("]");
        return list.toString();
    }

    
    /**
     * iterates through all indices in top to bottom order
     * @return iterator through all indices
     */
    public IntIterator iterator() {
        return new PiTIterator(this, true);
    }

    /**
     * iterates through all indices in bottom to top order
     * @return iterator through all indices in reverse order
     */
    public IntIterator reverseIterator() {
        return new PiTIterator(this, false);
    }

    public String toString() {
        if (this == getTopLevel()) {
            return "top level";
        }

        return "subterm: " + integerList(iterator());
    }

    public static final class PiTIterator implements IntIterator {
        private final PosInTerm pit;
        private int pos;
        private final boolean order;

        public PiTIterator(PosInTerm p, boolean order) {
            this.pit = p;
            this.order = order;
            this.pos = order ? 0 : p.size - 1;
        }

        @Override
        public int next() {
            if (pos < 0 || pos >= pit.size) {
                throw new IndexOutOfBoundsException();
            }

            int result = pit.positions[pos];

            if (order) {
                pos++;
            } else {
                pos--;
            }
            return result;
        }

        @Override
        public boolean hasNext() {
            return (order ? pos < pit.size : pos >= 0);
        }
    }


}