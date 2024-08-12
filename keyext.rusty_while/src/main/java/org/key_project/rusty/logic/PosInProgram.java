/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.rusty.ast.RustyProgramElement;

/**
 * this class describes the position of an expression in a program.
 */
public final class PosInProgram {
    /** pos at the beginning of the program */
    public static final PosInProgram TOP = new PosInProgram();

    /** often used positions */
    public static final PosInProgram ZERO = TOP.down(0);
    public static final PosInProgram ZERO_ZERO = ZERO.down(0);
    public static final PosInProgram ZERO_ONE = ZERO.down(1);
    public static final PosInProgram ONE = TOP.down(1);
    public static final PosInProgram ONE_ZERO = ONE.down(0);
    public static final PosInProgram ONE_ONE = ONE.down(1);


    /**
     * the position number
     */
    private final int[] pos;

    /**
     * pointer to the (last element + 1) in pos valid for this position
     */
    private final int depth;

    /**
     * returns the RustyProgramElement at the given position
     *
     * @param pos the PosInProgram
     * @param prg the RustyProgramElement we walk through
     * @return the RustyProgramElement at the given position
     * @throws IndexOutOfBoundsException if position <code>pos</code> refers to a non-existent
     *         program element
     */
    public static RustyProgramElement getProgramAt(PosInProgram pos, RustyProgramElement prg) {
        RustyProgramElement result = prg;
        for (int i = 0; i < pos.depth; i++) {
            // method getChildAt throws an array index out of bound if
            // it.next refers to a non-existing child
            result = (RustyProgramElement) result.getChild(pos.pos[i]);
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
     * creates a new PosInProgram position.
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

    /**
     * descending downwards choosing the n'th statement of the program
     *
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
        if (this != TOP && depth > 1) {
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

    private static PosInProgram add(PosInProgram first, PosInProgram second) {
        if (first == TOP) {
            return second;
        } else if (second == TOP) {
            return first;
        }

        final int[] newPos = new int[first.depth + second.depth];

        System.arraycopy(first.pos, 0, newPos, 0, first.depth);
        System.arraycopy(second.pos, 0, newPos, first.depth, second.depth);

        return new PosInProgram(newPos, newPos.length);
    }

    /**
     * compares this PosInProgram with another PosInProgram and returns true if both describe the
     * same position
     */
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }

        if (obj == null || this.getClass() != obj.getClass()) {
            return false;
        }

        final PosInProgram cmp = (PosInProgram) obj;

        if (depth != cmp.depth) {
            return false;
        }

        for (int i = 0; i < depth; i++) {
            if (cmp.pos[i] != pos[i]) {
                return false;
            }
        }
        return true;
    }

    public boolean leq(PosInProgram pip) {
        if (pip.depth < depth) {
            return false;
        }

        for (int i = 0; i < depth; i++) {
            if (pip.pos[i] < pos[i]) {
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
        return pos[depth - 1];
    }

    public RustyProgramElement getProgram(RustyProgramElement pe) {
        return getProgramAt(this, pe);
    }

    /**
     * returns an iterator over the list defining the position in a term.
     *
     * @return an iterator over the list defining the position in a term.
     */
    public IntIterator iterator() {
        return new PosArrayIntIterator(this);
    }



    /** toString */
    public String toString() {
        final StringBuilder list = new StringBuilder("\"PosInProgram: \"[");
        for (int i = 0; i < depth - 1; i++) {
            list.append(pos[i]).append(", ");
        }
        if (depth > 0) {
            list.append(pos[depth - 1]);
        }
        return list.append("]").toString();
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

    public int hashCode() {
        int hashCode = 0;
        for (int i : pos) {
            hashCode = 31 * hashCode + i;
        }
        return hashCode;
    }
}
