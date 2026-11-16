/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof;

import org.key_project.logic.sort.Sort;
import org.key_project.util.parsing.Position;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class SortMismatchException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = -5791743260310763761L;
    private final String toInstantiate;
    private final @Nullable Sort givenSort;

    /**
     * @param toInstantiate the term whose instantiation failed the sort check
     * @param givenSort the sort that was given for the instantiation, or {@code null} when the
     *        mismatch does not stem from a concrete given sort
     * @param position the position of the offending instantiation
     */
    public SortMismatchException(String toInstantiate, @Nullable Sort givenSort,
            Position position) {
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
