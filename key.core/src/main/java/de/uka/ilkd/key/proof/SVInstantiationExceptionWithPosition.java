/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;


import java.net.MalformedURLException;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;

/**
 * Represents an exception with position information. The row position is absolut this means, if in
 * a table it is the row of the table, but the column position is relative to the text and does not
 * describe the column of the table. (has to be changed)
 */
public abstract class SVInstantiationExceptionWithPosition extends SVInstantiationException
        implements HasLocation {

    private final Position position;
    private final boolean inIfSequent;

    public SVInstantiationExceptionWithPosition(String description, Position position,
            boolean inIfSequent) {
        super(description);
        this.position = position;
        this.inIfSequent = inIfSequent;

    }

    public boolean inIfSequent() {
        return inIfSequent;
    }

    public Position getPosition() {
        return position;
    }

    public String getMessage() {
        String msg = super.getMessage() + ":";
        if (!position.isNegative()) {
            if (inIfSequent()) {
                msg += "\nAssumption number:" + position.line();
            } else {
                msg += "\nRow: " + position.line();
                msg += "\nColumn: " + position.column();
            }
        }

        return msg;
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
        return new Location(null, position);
    }
}
