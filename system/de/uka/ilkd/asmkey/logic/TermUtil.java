// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;

/** Utility class with static methods for terms.
 *
 * @author Hubert Schmid
 */

public final class TermUtil {

    private TermUtil() {}

    /** empty array of terms. */
    private static final Term[] EMPTY_TERMS = new Term[] {};

    /** This methods calculates the maximum depth of an array of
     * terms. If the array is empty, the method returns
     * defaultValue. */
    protected static int maxDepth(Term[] terms, int defaultValue) {
        if (terms == null || terms.length == 0) {
            return defaultValue;
        } else {
            int max = terms[0].depth();
            for (int i = 1; i < terms.length; ++i) {
                int d = terms[i].depth();
                if (d > max) {
                    max = d;
                }
            }
            return max;
        }
    }

    /** This is used to print correctly the predicates
     * that are modalities. */
    public static int firstNonAsmSortIndex(Function f) {
	ArrayOfSort sorts = f.argSort();
	if (sorts == null || sorts.size() == 0) { return -1; }

	int result = 0;
	for (result = 0; result<sorts.size(); result++) {
	    if (sorts.getSort(result) != PrimitiveSort.ASMRULE) {
		break;
	    }
	}
	return result;
    }

}

