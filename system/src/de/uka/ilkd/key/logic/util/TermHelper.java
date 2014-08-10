// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.util;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Provides some helper methods used by classes outside the logic package
 * Please be careful with putting things here. This class has been mainly created
 * to give getMaxSort a home which is scheduled to become obsolete soon 
 * (see method comment)
 */
public class TermHelper {
    
    private TermHelper() {}

    /**
     * helper function to determine the maximal sort the term 
     * tSub may have as <tt>i</tt> sub term  
     * This method will become obsolete in the near future as all operators 
     * will become a fixed signature. But currently there ar eto many chnages 
     * pending (new sort hierarchy for integers, new pos) that much of the work would be 
     * for made new. That is the reason for this HACK 
     * @param term the Term of which a part of the <tt>i</tt>-th sub term 
     * may be replaced
     * @param i an int giving the position of sub term of which a part is to be replaced
     * @param services the Services object
     * @return the maximal sort allowed at the i-th position
     */
    public static Sort getMaxSort(Term term, int i, TermServices services) {     
        if (term.sub(i).sort() == Sort.FORMULA) return Sort.FORMULA;
        
        if (term.op() instanceof IfThenElse && i > 0) {
            return term.sort();
        }
        return getMaxSortHelper(term.op(), i, term.sub(i).sort(), services);                  
    }

    /**
     * @param op the Operator whose argument sorts are to be determined
     * @param i the arguments position
     * @param maxSortDefault if argument sort cannot be determined
     * @param services the Services object
     * @return the maximal sort allowed at argument <tt>i</tt>
     */
    private static Sort getMaxSortHelper(final Operator op, 
	    				 int i, 
	    				 Sort maxSortDefault,
	    				 TermServices services) {
        final Sort newMaxSort;
        if (op instanceof SortedOperator) {
            newMaxSort = ((SortedOperator)op).argSort(i);
        } else {                        
            newMaxSort = maxSortDefault;
        }
        return newMaxSort;
    }
}