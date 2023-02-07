/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.sort.Sort;


public class SortMismatchException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = -5791743260310763761L;
    private String toInstantiate;
    private Sort givenSort;

    public SortMismatchException(String toInstantiate, Sort givenSort, int row, int column) {
        super("Sorts mismatch", row, column, false);
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
