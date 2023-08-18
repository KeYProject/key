/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.logic.sort.Sort;


public class SortMismatchException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = -5791743260310763761L;
    private final String toInstantiate;
    private final Sort givenSort;

    public SortMismatchException(String toInstantiate, Sort givenSort, Position position) {
        super("Sorts mismatch", position, false);
        this.toInstantiate = toInstantiate;
        this.givenSort = givenSort;
    }

    public String getMessage() {
        String errmsg = super.getMessage();
        errmsg += "\n Sort of instantiation given for " + toInstantiate + ", " + givenSort
            + ", is illegal at this place.";
        return errmsg;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }
}
