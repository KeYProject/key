/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import recoder.ProgramFactory;

/**
 * A source element is a piece of syntax. It does not necessarily have a semantics, at least none
 * that is machinable, for instance a {@link recoder.java.Comment}.
 *
 * @author AL
 */

public interface SourceElement {

    /**
     * Finds the source element that occurs first in the source.
     *
     * @return the first source element in the syntactical representation of this element, may be
     *         equals to this element.
     * @see #toSource()
     * @see #getStartPosition()
     */
    SourceElement getFirstElement();

    /**
     * Finds the source element that occurs last in the source.
     *
     * @return the last source element in the syntactical representation of this element, may be
     *         equals to this element.
     * @see #toSource()
     * @see #getEndPosition()
     */
    SourceElement getLastElement();

    /**
     * Returns the start position of the primary token of this element. To get the start position of
     * the syntactical first token, call the corresponding method of <CODE>getFirstElement()</CODE>.
     *
     * @return the start position of the primary token.
     */
    Position getStartPosition();

    /**
     * Sets the start position of the primary token of this element. To set the start position of
     * the syntactical first token, call the corresponding method of <CODE>getFirstElement()</CODE>.
     *
     * @param p the start position of the primary token.
     */
    void setStartPosition(Position p);

    /**
     * Returns the end position of the primary token of this element. To get the end position of the
     * syntactical first token, call the corresponding method of <CODE>getLastElement()</CODE>.
     * <br>
     * The end position is <b>inclusive</b>.
     *
     * @return the end position of the primary token.
     */
    Position getEndPosition();

    /**
     * Sets the end position of the primary token of this element. To set the end position of the
     * syntactical first token, call the corresponding method of <CODE>getLastElement()</CODE>.
     *
     * @param p the end position of the primary token.
     */
    void setEndPosition(Position p);

    /**
     * Returns the relative position (number of blank heading lines and columns) of the primary
     * token of this element. To get the relative position of the syntactical first token, call the
     * corresponding method of <CODE>
     * getFirstElement()</CODE>.
     *
     * @return the relative position of the primary token.
     */
    Position getRelativePosition();

    /**
     * Sets the relative position (number of blank heading lines and columns) of the primary token
     * of this element. To set the relative position of the syntactical first token, call the
     * corresponding method of <CODE>
     * getFirstElement()</CODE>.
     *
     * @param p the relative position of the primary token.
     */
    void setRelativePosition(Position p);

    /**
     * Get factory.
     *
     * @return the program factory.
     */
    ProgramFactory getFactory();

    /**
     * Receive a visitor, for instance a pretty printer.
     *
     * @param v a source visitor.
     */
    void accept(SourceVisitor v);

    /**
     * Creates a syntactical representation of the source element using the {@link #accept}method
     * with an internal default pretty printer.
     */
    String toSource();

    /**
     * Creates a deep clone of the current source element. For {@link NonTerminalProgramElement}s,
     * the parent roles are valid, except that the root element is not included anywhere and hence
     * has no set parents, of course. This method also clones {@link recoder.java.Comment} s, but
     * does not clone derived information such as scopes.
     */
    SourceElement deepClone();

    /**
     * The position of a source element, given by its line and column number. Depending on the
     * implementation, the valid range of defined line and column numbers may be limited and cut off
     * if superceded.
     */

    class Position {

        /**
         * The "undefined position" constant used to compare to undefined positions or remove
         * positional information.
         */

        public final static Position UNDEFINED = new Position() {

            public void setLine(@SuppressWarnings("unused") int line) {
                throw new RuntimeException("Bad idea to redefine UNDEFINED Position");
            }

            public void setColumn(@SuppressWarnings("unused") int column) {
                throw new RuntimeException("Bad idea to redefine UNDEFINED Position");
            }

            public void setPosition(@SuppressWarnings("unused") int line,
                    @SuppressWarnings("unused") int column) {
                throw new RuntimeException("Bad idea to redefine UNDEFINED Position");
            }
        };
        /**
         * The line number.
         */

        private int line;
        /**
         * The column number.
         */

        private int column;

        /**
         * Constructs a new invalid source code position object.
         */

        Position() {
            line = column = -1;
        }

        /**
         * Constructs a new source code position object.
         *
         * @param line the line number.
         * @param column the column number.
         */

        public Position(int line, int column) {
            setPosition(line, column);
        }

        /**
         * Returns the line number of this position.
         *
         * @return the line number of this position.
         */

        public int getLine() {
            return line;
        }

        /**
         * Sets the line number of this position.
         *
         * @param line the future line number for this position (may not be negative).
         */

        public void setLine(int line) {
            if (line < 0) {
                throw new IllegalArgumentException("Negative line position " + line);
            }
            this.line = line;
            if (column < 0) {
                column = 0;
            }
        }

        /**
         * Returns the column number of this position.
         *
         * @return the column number of this position.
         */

        public int getColumn() {
            return column;
        }

        /**
         * Sets the column number of this position.
         *
         * @param column the future column number for this position (may not be negative).
         */

        public void setColumn(int column) {
            if (column < 0) {
                throw new IllegalArgumentException("Negative column position " + column);
            }
            this.column = column;
            if (line < 0) {
                line = 0;
            }
        }

        /**
         * Sets the line and column number of this position.
         *
         * @param line the future lkine number for this position (may not be negative).
         * @param column the future column number for this position (may not be negative).
         */

        public void setPosition(int line, int column) {
            if (line < 0) {
                throw new IllegalArgumentException("Negative line position " + line);
            }
            if (column < 0) {
                throw new IllegalArgumentException("Negative column position " + column);
            }
            this.line = line;
            this.column = column;
        }

        /**
         * Returns the hash code of this position.
         *
         * @return the hash code of this position.
         */

        public int hashCode() {
            return column | (line << 8);
        }

        /**
         * Compares this position with the given object for equality.
         *
         * @return <CODE>true</CODE>, if the given object is a position equals to this position,
         *         <CODE>false</CODE> otherwise.
         */

        public boolean equals(Object x) {
            if (x == this) {
                return true;
            }
            if (!(x instanceof Position)) {
                return false;
            }
            Position p = (Position) x;
            return line == p.line && column == p.column;
        }

        /**
         * Compares this position with the given object for order. An undefined position is less
         * than any defined position.
         *
         * @param x the position object to compare with.
         * @return a negative number, zero, or a positive number, if this position is lower than,
         *         equals to, or higher than the given one.
         */

        public int compareTo(Object x) {
            return compareTo((Position) x);
        }

        /**
         * Compares this position with the given object for order. An undefined position is less
         * than any defined position.
         *
         * @param p the position to compare with.
         * @return a negative number, zero, or a positive number, if this position is lower than,
         *         equals to, or higher than the given one.
         */

        public int compareTo(Position p) {
            return (line == p.line) ? (column - p.column) : (line - p.line);
        }

        /**
         * Returns a string representation of this object.
         */

        public String toString() {
            if (this != UNDEFINED) {
                return String.valueOf(line) + '/' + (column - 1);
            } else {
                return "??/??";
            }
        }
    }
}
