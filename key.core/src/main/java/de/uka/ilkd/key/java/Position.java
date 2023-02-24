package de.uka.ilkd.key.java;

/**
 * The position of a source element, given by its line and column number. Depending on the
 * implementation, the valid range of defined line and column numbers may be limited and cut off if
 * superceded.
 */

public class Position implements Comparable<Position> {

    /**
     * The line number.
     */

    private final int line;

    /**
     * The column number.
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
        this.line = line;
        this.column = column;
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
