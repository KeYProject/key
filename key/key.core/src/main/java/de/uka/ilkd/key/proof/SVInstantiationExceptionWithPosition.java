package de.uka.ilkd.key.proof;


import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;

import javax.annotation.Nullable;
import java.net.MalformedURLException;

/**
 * Represents an exception with position information. The row position is absolut this means, if in
 * a table it is the row of the table, but the column position is relative to the text and does not
 * describe the column of the table. (has to be changed)
 */
public abstract class SVInstantiationExceptionWithPosition extends SVInstantiationException
        implements HasLocation {

    private final int row;
    private final int column;
    private final boolean inIfSequent;

    public SVInstantiationExceptionWithPosition(String description, int row, int column,
            boolean inIfSequent) {
        super(description);
        this.row = row;
        this.column = column;
        this.inIfSequent = inIfSequent;

    }

    public boolean inIfSequent() {
        return inIfSequent;
    }

    public int getRow() {
        return row;
    }

    public int getColumn() {
        return column;
    }

    public String getMessage() {
        String errmsg = super.getMessage() + ":";
        if (inIfSequent()) {
            errmsg += row <= 0 ? "" : ("\nAssumption number:" + row);
        } else {
            errmsg += row <= 0 ? "" : ("\nRow: " + getRow());
            errmsg += column <= 0 ? "" : ("\nColumn: " + getColumn());
        }
        return errmsg;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        Location location;
        location = new Location((String) null, getRow(), getColumn());
        return location;
    }
}
