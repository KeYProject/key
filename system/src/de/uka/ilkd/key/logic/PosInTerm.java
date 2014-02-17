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
public class PosInTerm {

    private static final PosInTerm TOP_LEVEL = new PosInTerm();

    private final int[] positions;
    private final int size;
    private int hash = -1;

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
        positions = new int[0];
        size = 0;
        hash = 13;
    }

    /**
     * creates an instance representing the position <code>positions[0..size-1]</code>
     * @param positions the integer array where each element describes the position to be taken (in top-to-bottom order)
     * @param size the size of the integer list (attention: might be shorter than the length of the position array)
     */
    private PosInTerm(int[] positions, int size) {
        assert size > 0;
        this.positions = positions;
        this.size = size;
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
        return size == 1 ? getTopLevel() : new PosInTerm(positions, size - 1);
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
        return new PosInTerm(positions, n);
    }
    
    public PosInTerm down(int i) {
        final int[] newPositions = new int[size + 1];
        System.arraycopy(positions, 0, newPositions, 0, size);
        newPositions[size] = i;
        return new PosInTerm(newPositions, size + 1);
    }

    public int getIndexAt(int i) {
        if (i<0 || i>=size) {
            throw new IndexOutOfBoundsException("No position at index"+i);
        }
        return positions[i];
    }
    
    public int getIndex() {
        return size == 0 ? -1 : positions[size - 1];
    }

    public int hashCode() {        
        if (hash == -1) {
            hash = 13;
            for (int i = 0; i < size; i++) {
                hash = 13 * hash + positions[i];
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

    public IntIterator iterator() {
        return new PiTIterator(this, true);
    }

    public IntIterator reverseIterator() {
        return new PiTIterator(this, false);
    }

    public String toString() {
        if (this == getTopLevel()) {
            return "top level";
        }

        return "subterm: " + integerList(iterator());
    }

    public static class PiTIterator implements IntIterator {
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

    public static PosInTerm parseReverseString(String s) {
        if ("".equals(s)) {
            return getTopLevel();
        }
        
        final LinkedList<Integer> list = new LinkedList<Integer>();        
        final StringTokenizer tker = new StringTokenizer(s,",",false);
        
        while (tker.hasMoreTokens()) {
            list.addFirst(Integer.decode(tker.nextToken()));
        }
        
        final int[] positions = new int[list.size()];
        int i = 0;
        for (int j : list) {
            positions[i] = j;
            ++i;
        }
               
        return positions.length == 0 ? getTopLevel() : new PosInTerm(positions, positions.length);
    }

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

}
