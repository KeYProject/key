// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


/**
 * ensures that the types where the variables are declared are not the same
 */
public class TypeComparisionCondition extends VariableConditionAdapter {
    
    /** checks if sorts are not same */
    public final static int NOT_SAME = 0;
    /** checks if sorts are not compatible */
    public final static int NOT_COMPATIBLE = 1;
    /** checks subtype relationship */
    public final static int IS_SUBTYPE = 2;
    /** checks subtype relationship */
    public final static int NOT_IS_SUBTYPE = 3;
    /** check for strict subtype */
    public static final int STRICT_SUBTYPE = 4;
    /** checks if sorts are same */
    public final static int SAME = 5;

  
    private final int mode;
    private final TypeResolver fst;
    private final TypeResolver snd;


    /**
     * creates a condition that checks if the declaration types of the
     * schemavariable's instantiations are unequal 
     * @param fst one of the SchemaVariable whose type is checked
     * @param snd one of the SchemaVariable whose type is checked
     * @param mode an int encoding if testing of not same or not compatible
     */
    public TypeComparisionCondition (TypeResolver fst, 
				     TypeResolver snd,
				     int mode) {
	this.fst = fst;
	this.snd = snd;
	this.mode = mode;
    }
    

    /**
     * tests if the instantiations for both schema variables have a
     * different type
     * @param var the template Variable to be instantiated
     * @param subst the SVSubstitute to be mapped to var
     * @param svInst the SVInstantiations that are already known to be
     * needed
     * @return true iff condition is fulfilled
     */
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {
        
        if (!fst.isComplete(var, subst, svInst, services) ||
                !snd.isComplete(var, subst, svInst, services)) {
            // not yet complete
            return true;
        }
        
        
	return checkSorts(fst.resolveSort(var, subst, svInst, services), 
                snd.resolveSort(var, subst, svInst, services));
    }

    private boolean checkSorts(final Sort fstSort, final Sort sndSort) {
        switch (mode) {
        case SAME:
            return fstSort == sndSort;
        case NOT_SAME:
            return fstSort != sndSort;
        case NOT_COMPATIBLE:
            return !(fstSort.extendsTrans(sndSort) ||
        	     sndSort.extendsTrans(fstSort));
        case IS_SUBTYPE:        
            return fstSort.extendsTrans(sndSort);
        case STRICT_SUBTYPE:
            return fstSort != sndSort && fstSort.extendsTrans(sndSort);
        case NOT_IS_SUBTYPE:	    
            return !fstSort.extendsTrans(sndSort);        
        default:
            Debug.fail("TypeComparisionCondition: " + 
        	       "Unknown mode.");
            return false;
        }
    }

    public String toString () {
	switch (mode) {
        case SAME:
            return "\\same("+fst+", "+snd+")";
	case NOT_COMPATIBLE:
	    return "\\not\\compatible("+fst+", "+snd+")";
	case NOT_SAME:
	    return "\\not\\same("+fst+", "+snd+")";
	case IS_SUBTYPE:
	    return "\\sub(" + fst +", "+snd+")";
        case STRICT_SUBTYPE:
            return "\\strict\\sub(" + fst +", "+snd+")";
	case NOT_IS_SUBTYPE:
	    return "\\not\\sub("+fst+", "+snd+")";
	default:
	    return "invalid type copmparision mode";         	    
	}
    }

}
