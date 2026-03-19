/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.util;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.IfThenElse;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;


/**
 * Provides some helper methods used by classes outside the logic package Please be careful with
 * putting things here. This class has been mainly created to give getMaxSort a home which is
 * scheduled to become obsolete soon (see method comment)
 */
public class TermHelper {

    private TermHelper() {}

    /**
     * helper function to determine the maximal sort the term tSub may have as <tt>i</tt> sub term
     * This method will become obsolete in the near future as all operators will become a fixed
     * signature. But currently there ar eto many chnages pending (new sort hierarchy for integers,
     * new pos) that much of the work would be for made new. That is the reason for this HACK
     *
     * @param term the Term of which a part of the <tt>i</tt>-th sub term may be replaced
     * @param i an int giving the position of sub term of which a part is to be replaced
     * @return the maximal sort allowed at the i-th position
     */
    public static Sort getMaxSort(Term term, int i) {
        if (term.sub(i).sort() == JavaDLTheory.FORMULA) {
            return JavaDLTheory.FORMULA;
        }

        if (term.op() instanceof IfThenElse && i > 0) {
            return term.sort();
        }
        return getMaxSortHelper(term.op(), i, term.sub(i).sort());
    }

    /**
     * @param op the Operator whose argument sorts are to be determined
     * @param i the arguments position
     * @param maxSortDefault if argument sort cannot be determined
     * @return the maximal sort allowed at argument <tt>i</tt>
     */
    private static Sort getMaxSortHelper(final Operator op, int i, Sort maxSortDefault) {
        final Sort newMaxSort;
        if (op instanceof SortedOperator sortedOp) {
            newMaxSort = sortedOp.argSort(i);
        } else {
            newMaxSort = maxSortDefault;
        }
        return newMaxSort;
    }
}
