/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.pp;

import java.util.ArrayList;

/**
 * The intermediate layer of the pretty printing library. Using the block size information provided
 * by the {@link Layouter} class, this decides where to insert line breaks. It tries to break as few
 * blocks as possible.
 */

class Printer<M> {

    /**
     * Mask for break type flags. These flags are logically or-ed onto the margins in the
     * marginStack to remember what happens with the block in question.
     */
    private static final int BREAK_MASK = 0x70000000;
    /** Flag to indicate this block fits into the current line */
    private static final int FITS = 0x00000000;
    /** Flag to indicate this block will be broken consistently */
    private static final int CONSISTENT = 0x10000000;
    /** Flag to indicate this block will be broken inconsistently */
    private static final int INCONSISTENT = 0x20000000;

    /** total line length available */
    private int lineWidth;

    /** position in current line. */
    private int pos;

    /** Back-end for the pretty-printed output */
    private final StringBackend<M> back;

    /** stack to remember value of <code>pos</code> in nested blocks */
    private final ArrayList<Integer> marginStack = new ArrayList<>(10);


    /**
     * Create a printer. It will write its output to <code>writer</code>. Lines have a maximum width
     * of <code>lineWidth</code>.
     */
    Printer(StringBackend<M> back, int lineWidth) {
        this.back = back;
        this.lineWidth = lineWidth;
        pos = 0;
    }

    /** Line width */
    int lineWidth() {
        return lineWidth;
    }

    /** Sets the line width */
    void setLineWidth(int lineWidth) {
        this.lineWidth = lineWidth;
    }

    /** Accumulated result */
    String result() {
        return back.result();
    }

    /** The backend */
    StringBackend<M> backend() {
        return back;
    }

    /** write the String <code>s</code> to <code>out</code> */
    void print(String s) {
        back.print(s);
        pos += s.length();
    }

    /** begin a block */
    void openBlock(boolean consistent, boolean relative, int indent, int followingLength) {
        if (followingLength + pos > lineWidth) {
            int base;
            if (relative) {
                base = marginStack.isEmpty() ? 0 : topMargin();
            } else {
                base = pos;
            }
            push(base + indent, consistent ? CONSISTENT : INCONSISTENT);
        } else {
            push(0, FITS);
        }
    }

    /** end a block */
    void closeBlock() {
        pop();
    }

    /**
     * write a break. <code>followingLength</code> should be the space needed by the material up to
     * the next corresponding closeBlock() or printBreak(), and is used to decide whether the
     * current line is continues, or a new (indented) line is begun.
     */
    void printBreak(int width, int offset, int followingLength) {
        if (topBreak() == CONSISTENT
                || (topBreak() == INCONSISTENT && followingLength > (lineWidth - pos))) {

            pos = topMargin() + offset;

            newLine();
        } else {
            writeSpaces(width);
            pos += width;
        }
    }

    void mark(M o) {
        back.mark(o);
    }

    void indent(int width, int offset) {
        int newMargin = topMargin() + offset;
        if (topBreak() != FITS) {
            if (newMargin > pos) {
                writeSpaces(newMargin - pos);
                pos = newMargin;
            }
        } else {
            writeSpaces(width);
            pos += width;
        }
    }

    /** Return the amount of space currently left on this line. */
    int space() {
        return lineWidth - pos;
    }

    private void push(int n, int breaks) {
        marginStack.add(n | breaks);
    }

    /** Pop one element from the space stack. */
    private void pop() {
        try {
            marginStack.remove(marginStack.size() - 1);
        } catch (IndexOutOfBoundsException e) {
            throw new UnbalancedBlocksException();
        }
    }

    /** return the topmost element of the space stack without popping it. */
    private int top() {
        try {
            return marginStack.get(marginStack.size() - 1);
        } catch (IndexOutOfBoundsException e) {
            throw new UnbalancedBlocksException();
        }
    }

    private int topMargin() {
        return top() & ~BREAK_MASK;
    }

    private int topBreak() {
        return top() & BREAK_MASK;
    }

    /**
     * Start a new line and indent according to <code>pos</code>
     */
    private void newLine() {
        back.newLine();
        if (pos > 0) {
            writeSpaces(pos);
        }
    }

    /** how many spaces */
    private static final int SPACES = 128;

    /** a String containing <code>SPACES</code> spaces */
    private static final String spaces = " ".repeat(SPACES);

    private void writeSpaces(int n) {
        while (n > SPACES) {
            back.print(spaces);
            n -= SPACES;
        }
        back.print(spaces.substring(0, n));
    }
}
