// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic.sort;

import de.uka.ilkd.key.logic.sort.IteratorOfSort;
import de.uka.ilkd.key.logic.sort.NonCollectionSort;
import de.uka.ilkd.key.logic.sort.Sort;

/** Utility class with static methods for sorts.
 *
 * @author Hubert Schmid
 */

public final class SortUtil {

    private SortUtil() {}

    /** Determines if the sort 'lhs' extends the sort 'rhs'. */
    public static boolean extendsTrans(Sort lhs, Sort rhs) {
        if (lhs == rhs) {
            return true;
        }
        for (IteratorOfSort i = lhs.extendsSorts().iterator(); i.hasNext();) {
            Sort s = i.next();
            if (s == rhs || extendsTrans(s, rhs)) {
                return true;
            }
        }
        return false;
    }

    /** Returns 'true' if the given sort is a primitive sort. */
    public static boolean isPrimitiveSort(Sort sort) {
        return sort instanceof PrimitiveSort || sort == Sort.FORMULA;
    }

    public static boolean isSequenceSortOf(Sort basicSort, Sort seqSort) {
	/*if (seqSort == CollectionSort.SEQGENERIC) {
	    return true;
	    } else {*/
	    if (basicSort instanceof NonCollectionSort) {
		NonCollectionSort ns = (NonCollectionSort) basicSort;
		return ns.getSequenceSort() == seqSort;
	    }
	    //}
	return false;
    }

}
