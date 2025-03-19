/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import java.io.Serializable;

import recoder.ProgramFactory;

/**
 * Top level implementation of a Java {@link SourceElement}. This class already knows its
 * {@link ProgramFactory}.
 *
 * @author AL
 */

public abstract class JavaSourceElement implements SourceElement, Cloneable, Serializable {

    /**
     * The JavaProgramFactory.
     */

    protected static final JavaProgramFactory factory = JavaProgramFactory.getInstance();

    /**
     * Position bit encoding. Internal format is start line: 16 | start column: 8 | end line: 16 |
     * end column: 8 | blank lines: 8 | blank columns: 8.
     */

    private long positionBits = 0xFFFFFFFFFFFFFFFFL;

    /**
     * Java source element.
     */

    public JavaSourceElement() {
        // nothing to do here
    }

    /**
     * Java source element.
     *
     * @param proto a java source element.
     */

    protected JavaSourceElement(JavaSourceElement proto) {
        if (proto == null) {
            throw new NullPointerException("Cannot create something from a null prototype.");
        }
        positionBits = proto.positionBits;
    }

    /**
     * Finds the source element that occurs first in the source. The default implementation returns
     * this element, which is correct for all terminal program elements, and many non terminals such
     * as statements and prefixed operators.
     *
     * @return the first source element in the syntactical representation of this element, may be
     *         equals to this element.
     * @see #toSource()
     * @see #getStartPosition()
     */

    public SourceElement getFirstElement() {
        return this;
    }

    /**
     * Finds the source element that occurs last in the source. The default implementation returns
     * this element, which is correct for all terminal program elements, and many non terminals such
     * as statements and prefixed operators.
     *
     * @return the last source element in the syntactical representation of this element, may be
     *         equals to this element.
     * @see #toSource()
     * @see #getEndPosition()
     */

    public SourceElement getLastElement() {
        return this;
    }

    /**
     * Returns the start position of the primary token of this element. To get the start position of
     * the syntactical first token, call the corresponding method of <CODE>getFirstElement()</CODE>.
     *
     * @return the start position of the primary token.
     */

    public final Position getStartPosition() {
        int lc = (int) (positionBits >> 40L) & 0xFFFFFF;
        if (lc == 0xFFFFFF) {
            return Position.UNDEFINED;
        }
        return new Position(lc >> 8, lc & 0xFF);
    }

    /**
     * Sets the start position of the primary token of this element. To set the start position of
     * the syntactical first token, call the corresponding method of <CODE>getFirstElement()</CODE>.
     *
     * @param p the start position of the primary token.
     */

    public final void setStartPosition(Position p) {
        if (p == Position.UNDEFINED) {
            positionBits |= 0xFFFFFF0000000000L;
        } else {
            int lc = (Math.min(p.getLine(), 0xFFFE) << 8) | Math.min(p.getColumn(), 0xFF);
            positionBits &= 0x000000FFFFFFFFFFL;
            positionBits |= ((long) lc << 40L);
        }
    }

    /**
     * Returns the end position of the primary token of this element. To get the end position of the
     * syntactical first token, call the corresponding method of <CODE>getLastElement()</CODE>.
     *
     * @return the end position of the primary token.
     */

    public final Position getEndPosition() {
        int lc = (int) (positionBits >> 16L) & 0xFFFFFF;
        if (lc == 0xFFFFFF) {
            return Position.UNDEFINED;
        }
        return new Position(lc >> 8, lc & 0xFF);
    }

    /**
     * Sets the end position of the primary token of this element. To set the end position of the
     * syntactical first token, call the corresponding method of <CODE>getLastElement()</CODE>.
     *
     * @param p the end position of the primary token.
     */

    public final void setEndPosition(Position p) {
        if (p == Position.UNDEFINED) {
            positionBits |= 0x000000FFFFFF0000L;
        } else {
            int lc = (Math.min(p.getLine(), 0xFFFE) << 8) | Math.min(p.getColumn(), 0xFF);
            positionBits &= 0xFFFFFF000000FFFFL;
            positionBits |= ((long) lc << 16L);
        }
    }

    /**
     * Returns the relative position (number of blank heading lines and columns) of the primary
     * token of this element. To get the relative position of the syntactical first token, call the
     * corresponding method of <CODE>
     * getFirstElement()</CODE>.
     *
     * @return the relative position of the primary token.
     */

    public final Position getRelativePosition() {
        int lc = (int) positionBits & 0xFFFF;
        if (lc == 0xFFFF) {
            return Position.UNDEFINED;
        }
        return new Position(lc >> 8, lc & 0xFF);
    }

    /**
     * Sets the relative position (number of blank heading lines and columns) of the primary token
     * of this element. To set the relative position of the syntactical first token, call the
     * corresponding method of <CODE>
     * getFirstElement()</CODE>.
     *
     * @param p the relative position of the primary token.
     */

    public final void setRelativePosition(Position p) {
        if (p == Position.UNDEFINED) {
            positionBits |= 0x000000000000FFFFL;
        } else {
            int lc = (Math.min(p.getLine(), 0xFE) << 8) | Math.min(p.getColumn(), 0xFF);
            positionBits &= 0xFFFFFFFFFFFF0000L;
            positionBits |= lc;
        }
    }

    /**
     * Get factory.
     *
     * @return the program factory.
     */

    public final ProgramFactory getFactory() {
        return factory;
    }

    public String toSource() {
        return factory.toSource(this);
    }

    public String toString() {
        return getClass().getName() + "@" + getStartPosition();
    }
}
