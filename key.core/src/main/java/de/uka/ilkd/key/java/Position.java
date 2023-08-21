/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import org.antlr.v4.runtime.Token;
import recoder.java.SourceElement;

/**
 * The position of a source element, given by its line and column number. Depending on the
 * implementation, the valid range of defined line and column numbers may be limited and cut off if
 * superceded.
 */

public class Position implements Comparable<Position> {

    /**
     * The line number, 1-based.
     */
    private final int line;

    /**
     * The column number, 1-based.
     */
    private final int column;

    /**
     * The "undefined position" constant used to compare to undefined positions or remove positional
     * information.
     */
    public static final Position UNDEFINED = new Position();

    /**
     * Constructs a new invalid source code position object.
     */
    private Position() {
        line = column = -1;
    }

    /**
     * Constructs a new source code position object.
     *
     * @param line the line number.
     * @param column the column number.
     */
    private Position(int line, int column) {
        if (line < 1 || column < 1) {
            throw new IllegalArgumentException(line + ", " + column);
        }
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
     * Creates a new Location with 1-based line and 0-based column numbers.
     * This format is used by most parsers so this deserves an explicit method call.
     *
     * @param line_1 1-based line of the Location
     * @param column_0 0-based column of the Location
     */
    public static Position fromOneZeroBased(int line_1, int column_0) {
        return new Position(line_1, column_0 + 1);
    }

    /**
     * Creates a new location from a token.
     *
     * @param token the token
     */
    public static Position fromToken(Token token) {
        return fromOneZeroBased(token.getLine(), token.getCharPositionInLine());
    }

    /**
     * Creates a new location from a token.
     *
     * @param token the token
     */
    public static Position fromToken(de.uka.ilkd.key.parser.proofjava.Token token) {
        return new Position(token.beginLine, token.beginColumn);
    }

    /**
     * Creates a new location from a SourceElement position.
     *
     * @param pos the position
     */
    public static Position fromSEPosition(SourceElement.Position pos) {
        if (pos == SourceElement.Position.UNDEFINED) {
            return UNDEFINED;
        } else if (pos.getColumn() == 0) {
            // This is a hack, some recoder positions have column 0 (not set)
            // even though the column is 0-based *and* -1 is the unset value
            // return new Position(pos.getLine(), 1);
            throw new IllegalArgumentException("ProofJava produced column 0");
        } else {
            return new Position(pos.getLine(), pos.getColumn());
        }
    }

    /**
     * Creates a new Position with the offset added to the line.
     *
     * @param offset the offset
     */
    public Position offsetLine(int offset) {
        return new Position(line + offset, column);
    }

    /**
     * Returns the line number of this position.
     *
     * @return the line number of this position.
     */
    public int line() {
        return line;
    }

    /**
     * Returns the column number of this position.
     *
     * @return the column number of this position.
     */
    public int column() {
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
     * Compares this position with the given object for order. An undefined position is less than
     * any defined position.
     *
     * @param p the position to compare with.
     * @return a negative number, zero, or a positive number, if this position is lower than, equals
     *         to, or higher than the given one.
     */
    @Override
    public int compareTo(Position p) {
        return (line == p.line) ? (column - p.column) : (line - p.line);
    }

    /**
     * Helper method for validity checks.
     *
     * @return true iff either line or column are negative
     */
    public boolean isNegative() {
        return line <= 0 || column <= 0;
    }

    /**
     * Returns a string representation of this object.
     */
    public String toString() {
        if (this != UNDEFINED) {
            return String.valueOf(line) + '/' + column;
        } else {
            return "??/??";
        }
    }
}
