package de.uka.ilkd.key.logic.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
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
    public static Sort getMaxSort(Term term, int i, Services services) {       
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
	    				 Services services) {
        final Sort newMaxSort;
        if (op instanceof Function) {
            newMaxSort = ((Function)op).argSort(i);
        } else if (i == 0 && op instanceof AttributeOp) {          
            newMaxSort = ((AttributeOp)op).getContainerType().getSort();
        } else if (i == 0 && op instanceof ArrayOp) {
            newMaxSort = ((ArrayOp)op).arraySort();
        } else if (op instanceof AccessOp) {
            newMaxSort = 
        	services.getTypeConverter().getIntegerLDT().targetSort();
        } else if (op instanceof Equality) {
            newMaxSort = ((Equality)op).argSort(i);
        } else if (op instanceof IUpdateOperator) {
            newMaxSort = maxSortIUpdate( (IUpdateOperator) op, 
        	    			  i, 
        	    			  maxSortDefault, 
        	    			  services );
        } else {                        
            newMaxSort = maxSortDefault;
        }
        return newMaxSort;
    }
    
    /**
     * 
     * looks up if the given subterm position describes a value
     */
    private static Sort maxSortIUpdate(IUpdateOperator op, 
	    			       int pos, 
	    			       Sort maxSortDefault,
	    			       Services services) {
        if (op.targetPos() != pos) { 
            for (int i = 0, locs = op.locationCount(); i<locs; i++) {
                final int valuePos = op.valuePos(i);
                if (valuePos == pos) {
                    return Sort.ANY; //op.location(i).sort() would be more precise
                                     // but the current solution is also sound
                                     // as the update application rules take care
                                      // of inserting casts when necessary
                } else if (pos < valuePos) {
                    if (op.locationSubtermsBegin(i) <= pos && 
                            pos < op.locationSubtermsEnd(i)) {                   
                        return getMaxSortHelper(op.location(i), 
                                pos-op.locationSubtermsBegin(i), 
                                maxSortDefault,
                                services);
                    }
                }
            }
        }
        return maxSortDefault;
    }

}
