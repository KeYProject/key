// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule.conditions;


import java.util.Map;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * General varcond for checking relationships between types of schema variables.
 */
public final class TypeComparisonCondition extends VariableConditionAdapter {
    
    public static enum Mode 
                {NOT_SAME,           /* checks if sorts are not same */
	         SAME,               /* checks if sorts are same */ 
	         IS_SUBTYPE,         /* checks subtype relationship */
	         NOT_IS_SUBTYPE,     /* checks subtype relationship */
	         STRICT_SUBTYPE,     /* checks for strict subtype */
	         DISJOINTMODULONULL} /* checks if sorts are disjoint */
    
    private final Mode mode;
    private final TypeResolver fst;
    private final TypeResolver snd;


    /**
     * creates a condition that checks if the declaration types of the
     * schemavariable's instantiations are unequal 
     * @param fst one of the SchemaVariable whose type is checked
     * @param snd one of the SchemaVariable whose type is checked
     * @param mode an int encoding if testing of not same or not compatible
     */
    public TypeComparisonCondition(TypeResolver fst, 
				   TypeResolver snd,
				   Mode mode) {
	this.fst = fst;
	this.snd = snd;
	this.mode = mode;
    }
    
    
    public TypeResolver getFirstResolver(){
	return fst;
    }
    
    
    public TypeResolver getSecondResolver(){
	return snd;
    }
    

    public Mode getMode(){
	return mode;
    }
    
    @Override
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {
        
        if (!fst.isComplete(var, subst, svInst, services) 
             || !snd.isComplete(var, subst, svInst, services)) {
            // not yet complete
            return true;
        }
        Sort fstSort = fst.resolveSort(var, subst, svInst, services);
        Sort sndSort = snd.resolveSort(var, subst, svInst, services);
        if(fstSort instanceof GenericSort || sndSort instanceof GenericSort) {
            return false;
        }
        return checkSorts(fstSort, sndSort, services);
    }

    
    private boolean checkSorts(final Sort fstSort, 
	                       final Sort sndSort, 
	                       final Services services) {
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
            assert false;
            return false;
        }
    }
    
    
    private static Map<Sort,Map<Sort,Boolean>> disjointnessCache 
    	= new WeakHashMap<Sort,Map<Sort,Boolean>>();
    
    
    private static Boolean lookupInCache(Sort s1, Sort s2) {
	Boolean result = null;
	
	Map<Sort,Boolean> map = disjointnessCache.get(s1);
	if(map != null) {
	    result = map.get(s2);
	}
	
	if(result == null) {
	    map = disjointnessCache.get(s2);
	    if(map != null) {
		result = map.get(s1);
	    }	    
	}
	
	return result;
    }
    
    
    private static void putIntoCache(Sort s1, Sort s2, boolean b) {
	Map<Sort,Boolean> map = disjointnessCache.get(s1);
	if(map == null) {
	    map = new WeakHashMap<Sort,Boolean>();
	}
	map.put(s2, b);
	disjointnessCache.put(s1, map);
    }
    
    
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
	Boolean result = lookupInCache(fstSort, sndSort);
	
	//if not, compute it 
	if(result == null) {
	    final JavaInfo javaInfo = services.getJavaInfo();
	    
	    //array sorts are disjoint if their element sorts are disjoint
	    Sort fstElemSort = fstSort;
	    Sort sndElemSort = sndSort;
	    while(fstElemSort instanceof ArraySort 
	          && sndElemSort instanceof ArraySort) {
		fstElemSort = ((ArraySort)fstElemSort).elementSort();
		sndElemSort = ((ArraySort)sndElemSort).elementSort();
	    }
	    
	    //object sorts?
	    final Sort objectSort = services.getJavaInfo().objectSort();	    
	    boolean fstElemIsObject = fstElemSort.extendsTrans(objectSort);
	    boolean sndElemIsObject = sndElemSort.extendsTrans(objectSort);
	    
	    //try to get KeYJavaTypes (only works for types existing in program)
	    final KeYJavaType fstKJT = javaInfo.getKeYJavaType(fstSort);
	    final KeYJavaType sndKJT = javaInfo.getKeYJavaType(sndSort);
	    
	    if(fstElemIsObject 
	       && sndElemIsObject
	       && !(fstElemSort instanceof ArraySort)
	       && !(sndElemSort instanceof ArraySort)
	       && (fstKJT != null && fstKJT.getJavaType() 
		       	instanceof InterfaceDeclaration
		   || sndKJT != null && sndKJT.getJavaType() 
		   	instanceof InterfaceDeclaration)) {
		//be conservative wrt. modularity: program extensions may add 
		//new subtypes between object sorts, if none of them is
		//an array sort and at least one of them is an interface sort
		result = false;
	    } else {
		//otherwise, we just check whether *currently* there is 
		//some common subsort
		result = true;
		for(Named n : services.getNamespaces().sorts().allElements()) {
		    final Sort s = (Sort) n;
		    if(!(s instanceof NullSort)
		         && s.extendsTrans(fstSort)
			 && s.extendsTrans(sndSort)) {
			result = false;
			break;
		    }
		}
	    }
	    
    	    putIntoCache(fstSort, sndSort, result);
    	}
	
	return result;
    }

    
    @Override    
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
