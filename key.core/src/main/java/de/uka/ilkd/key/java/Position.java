/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.java;

import recoder.java.SourceElement;

/**
 * The position of a source element, given by its line and column
 * number.
 * Depending on the implementation, the valid range of defined line and
 * column numbers may be limited and cut off if superceded.
 */

public class Position {

    /**
     * The line number.
     */

    private final int line;

    /**
     * The column number.
     */

    private final int column;

    /**
     * The "undefined position" constant used to compare to undefined
     * positions or remove positional information.
     */
    public static final Position UNDEFINED = new Position();

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

        /*if (line < 1 || column < 1) {
            throw new IllegalArgumentException(line + "," + column);
        }*/
        this.line = line;
        this.column = column;
    }

    /**
     * Creates a new Location with 1-based line and 1-based column numbers.
     *
     * @param line_1 1-based line of the Location
     * @param column_0 1-based column of the Location
     */
    public static Position newOneBased(int line_1, int column_0) {
        return new Position(line_1, column_0);
    }

    /**
     * Creates a new location from a SourceElement position.
     *
     * @param pos the position
     */
    public static Position fromSEPosition(recoder.java.SourceElement.Position pos) {
        if (pos == SourceElement.Position.UNDEFINED) {
            return UNDEFINED;/*
        } else if (pos.getColumn() == 0) {
            // This is a hack, some recoder positions have column 0 (not set)
            // even though the column is 0-based *and* -1 is the unset value
            // return new Position(pos.getLine(), 1);
            throw new IllegalArgumentException("ProofJava produced column 0");*/
        } else {
            return new Position(pos.getLine(), pos.getColumn());
        }
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
     * Returns the column number of this position.
     *
     * @return the column number of this position.
     */

    public int getColumn() {
        return column;
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
     * @return <CODE>true</CODE>, if the given object is a position
     *         equals to this position, <CODE>false</CODE> otherwise.
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
     * Compares this position with the given object for order.
     * An undefined position is less than any defined position.
     *
     * @param x the position object to compare with.
     * @return a negative number, zero, or a positive number, if this
     *         position is lower than, equals to, or higher than the given one.
     */
    public int compareTo(Object x) {
        return compareTo((Position) x);
    }

    /**
     * Compares this position with the given object for order.
     * An undefined position is less than any defined position.
     *
     * @param p the position to compare with.
     * @return a negative number, zero, or a positive number, if this
     *         position is lower than, equals to, or higher than the given one.
     */
    public int compareTo(Position p) {
        return (line == p.line) ? (column - p.column) : (line - p.line);
    }

    /**
     * Helper method for validity checks.
     *
     * @return true iff either line or column are negative
     */
    public boolean isNegative() {
        return line < 0 || column < 0;
    }

    /**
     * Returns a string representation of this object.
     */
    public String toString() {
        if (this != UNDEFINED) {
            StringBuffer buf = new StringBuffer();
            buf.append(line).append('/').append(column - 1);
            return buf.toString();
        } else {
            return "??/??";
        }
    }

}
