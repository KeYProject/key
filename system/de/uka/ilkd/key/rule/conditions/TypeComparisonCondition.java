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


import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;
import de.uka.ilkd.key.logic.sort.SetOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


/**
 * ensures that the types where the variables are declared are not the same
 */
public class TypeComparisonCondition extends VariableConditionAdapter {
    
    /** checks if sorts are not same */
    public final static int NOT_SAME = 0;

    /** checks subtype relationship */
    public final static int IS_SUBTYPE = 2;
    /** checks subtype relationship */
    public final static int NOT_IS_SUBTYPE = 3;
    /** check for strict subtype */
    public static final int STRICT_SUBTYPE = 4;
    /** checks if sorts are same */
    public final static int SAME = 5;
    /** checks if sorts are disjoint */
    public final static int DISJOINTMODULONULL = 6; //XXX

  
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
    public TypeComparisonCondition (TypeResolver fst, 
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
                snd.resolveSort(var, subst, svInst, services), services);
    }

    private boolean checkSorts(final Sort fstSort, final Sort sndSort, Services services) {
        switch (mode) {
        case SAME:
            return fstSort == sndSort;
        case NOT_SAME:
            return fstSort != sndSort;
        case IS_SUBTYPE:        
            return fstSort.extendsTrans(sndSort);
        case STRICT_SUBTYPE:
            return fstSort != sndSort && fstSort.extendsTrans(sndSort);
        case NOT_IS_SUBTYPE:	    
            return !fstSort.extendsTrans(sndSort);        
        case DISJOINTMODULONULL:
            return checkDisjointness(fstSort, sndSort, services);
        default:
            Debug.fail("TypeComparisionCondition: " + 
        	       "Unknown mode.");
            return false;
        }
    }
    
    
    private Map<SetOfSort,Boolean> disjointnessCache 
    	= new HashMap<SetOfSort,Boolean>();
    
    /**
     * Checks for disjointness modulo "null".
     */
    private boolean checkDisjointness(Sort fstSort, 
	    			      Sort sndSort, 
	    			      Services services) {
	//sorts identical?
	if(fstSort == sndSort) {
	    return false;
	}
	
	//result cached?
	SetOfSort sorts = SetAsListOfSort.EMPTY_SET.add(fstSort).add(sndSort);	
	Boolean result = disjointnessCache.get(sorts);
	if(result == null) {
	    //compute result
	    result = true;
    	    for(Named n : services.getNamespaces().sorts().allElements()) {
    		Sort s = (Sort) n;
    		if(!(s instanceof NullSort) 
    			&& s.extendsTrans(fstSort) 
    			&& s.extendsTrans(sndSort)) {
    		    result = false;
    		    break;
    		}
    	    }
    	    disjointnessCache.put(sorts, result);
    	}
	
	return result;
    }

    public String toString () {
	switch (mode) {
        case SAME:
            return "\\same("+fst+", "+snd+")";
	case NOT_SAME:
	    return "\\not\\same("+fst+", "+snd+")";
	case IS_SUBTYPE:
	    return "\\sub(" + fst +", "+snd+")";
        case STRICT_SUBTYPE:
            return "\\strict\\sub(" + fst +", "+snd+")";
	case NOT_IS_SUBTYPE:
	    return "\\not\\sub("+fst+", "+snd+")";
	case DISJOINTMODULONULL:
	    return "\\disjointModuloNull("+fst+", "+snd+")";
	default:
	    return "invalid type comparison mode";         	    
	}
    }
}
