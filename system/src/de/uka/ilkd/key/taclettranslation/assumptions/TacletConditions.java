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
 

package de.uka.ilkd.key.taclettranslation.assumptions;

import java.util.Iterator;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.conditions.AbstractOrInterfaceType;
import de.uka.ilkd.key.rule.conditions.ArrayComponentTypeCondition;
import de.uka.ilkd.key.rule.conditions.TypeComparisonCondition;
import de.uka.ilkd.key.rule.conditions.TypeCondition;
import de.uka.ilkd.key.rule.conditions.TypeComparisonCondition.Mode;
import de.uka.ilkd.key.rule.conditions.TypeResolver.GenericSortResolver;
import de.uka.ilkd.key.rule.conditions.TypeResolver.NonGenericSortResolver;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;

/**
 * This class is used for wrapping all variable conditions of a taclet
 * in one object. 
 */
class TacletConditions {

//    
    private ImmutableList<TypeComparisonCondition> 
    		comparisionCondition = ImmutableSLList.nil();
    private ImmutableList<TypeCondition> typeCondition = ImmutableSLList.nil();
    private ImmutableList<AbstractOrInterfaceType> abstractInterfaceCondition 
    		= ImmutableSLList.nil();
    private ImmutableList<ArrayComponentTypeCondition>
    		arrayComponentCondition = ImmutableSLList.nil();  

    
    
  
    public final static int FALSE = 0;
    public final static int NULL_LEGAL = 1;
    public final static int NULL_ILLEGAL = 2;
  
      
    
    public TacletConditions(Taclet t) throws IllegalTacletException{
	
	Iterator<VariableCondition> it = t.getVariableConditions();
	

	while(it.hasNext()){
	    boolean supported = false;
	    VariableCondition cond = it.next();

	    if(cond instanceof TypeComparisonCondition){
		comparisionCondition = 
		    comparisionCondition.append((TypeComparisonCondition)cond);
		supported = true;
	    }
	    if(cond instanceof TypeCondition){
		typeCondition = typeCondition.append((TypeCondition)cond);
		supported = true;
	    }
	    if(cond instanceof AbstractOrInterfaceType){
		abstractInterfaceCondition =
		    abstractInterfaceCondition.append((
			    AbstractOrInterfaceType) cond);
		supported = true;
	    }
	    if(cond instanceof ArrayComponentTypeCondition){
		arrayComponentCondition = 
		    arrayComponentCondition.append(
			    (ArrayComponentTypeCondition)cond);
		supported = true;
	    }
	    if(!supported){
		throw new IllegalTacletException("Condition " + cond.getClass().getSimpleName() + " is" +
	    		" not supported.");
	    }
	}

    }
    
    public boolean containsIsReferenceArray(Term t){
	
	for(ArrayComponentTypeCondition cond : arrayComponentCondition){
	    
	    if(cond.isCheckReferenceType() ){
		return true;
	    }
	    
	}
	return false;
    }
    
    /**
     * Checks whether the conditions contains a "\not\isAbstractOrInterface"
     * condition for the sort <code>s</code>.
     * @param s
     * @return <code>true</code> if there is such a condition, 
     * otherwise <code>false</code>.
     */
    public boolean containsNotAbstractInterfaceCondition(Sort s){
	return containsAbstractInterfaceCondition(s,true);
    }
    
    /**
     * Checks whether the conditions contains a "\isAbstractOrInterface"
     * condition for the sort <code>s</code>.
     * @param s
     * @return <code>true</code> if there is such a condition, 
     * otherwise <code>false</code>.
     */
    public boolean containsAbstractInterfaceCondition(Sort s){
	return containsAbstractInterfaceCondition(s, false);
    }
    
    private boolean containsAbstractInterfaceCondition(Sort s, boolean negated){
	for(AbstractOrInterfaceType cond : abstractInterfaceCondition){
	     if((negated && cond.isNegated()) || (!negated && !cond.isNegated())){
		 if(cond.getTypeResolver() instanceof GenericSortResolver){

			GenericSortResolver res = (GenericSortResolver)cond.getTypeResolver();
			if(res.getGenericSort().equals(s)){
			    return true;
			}
		     
		 }
		 
	     }
	}    
	return false;
    }

    
    
    
    /**
     * Checks whether the conditions contains the "notSame"-condition
     * with the corresponding sorts <code>s1</code> and <code>s2</code>.
     * @param s1 
     * @param s2
     * @return <code>true</code> if there is such a condition, 
     * otherwise <code>false</code>.
     */
    public boolean containsNotSameCondition(Sort s1, Sort s2){
	return conatainsComparisionConditionSymmetric(s1, s2,
		TypeComparisonCondition.Mode.NOT_SAME);

    }
    
    /**
     * Does the same like <code>containsComparisionCondition</code> with 
     * the difference, that the order of <code>s1</code> and <code>s2</code>
     * is not important.
     */    
    public boolean conatainsComparisionConditionSymmetric(Sort s1,
	    Sort s2, TypeComparisonCondition.Mode mode){
	if(!containsComparisionCondition(s1, s2, mode)){
	    if(containsComparisionCondition(s2, s1, mode)) return true;
	}else{return true;}
	return false;
    }
    
    /**
     * Returns whether the taclet has a type comparision condition according
     * to the sorts <code> s1</code> and <code>s2</code>.<br>
     * REMARK: The right order of <code>s1</code> and <code>s2</code> is important.
     * For symmetric conditions like "notSame" use 
     * <code>containsNotSameConditionSymmetric</code>.
     * @param s1 
     * @param s2
     * @param mode see {@link TypeComparisonCondition}
     * @return <code>true</code> if the taclet contains the condition,
     *  otherwise false.
     */    
    public boolean containsComparisionCondition(Sort s1, Sort s2, TypeComparisonCondition.Mode mode){
	
	for(TypeComparisonCondition tcc : comparisionCondition){
	    if(containsComparisionCondition(tcc, s1, s2,mode)){
		return true;
	    }
	}

	return false;
    }
    
    private boolean containsComparisionCondition(TypeComparisonCondition tcc,
	    Sort s1, Sort s2, TypeComparisonCondition.Mode mode){
	
        GenericSortResolver first  = null, second = null;
	
        if(tcc.getFirstResolver() instanceof GenericSortResolver){
            first = (GenericSortResolver)tcc.getFirstResolver();
        }

        if(tcc.getSecondResolver() instanceof GenericSortResolver){
            second = (GenericSortResolver)tcc.getSecondResolver();
        }


        if(first != null && second != null){
            if(tcc.getMode() == mode){
                if(first.getGenericSort().equals(s1) &&
                        second.getGenericSort().equals(s2)){
                    return true;}
                if(first.getGenericSort().equals(s2) &&
                        second.getGenericSort().equals(s1)){
                    return true;}
            }
        }
        return false;

    }
    
    public boolean containsIsSubtypeRelation(Sort gen,Sort inst, TypeComparisonCondition.Mode mode){
	for(TypeComparisonCondition tcc : comparisionCondition){
	    if(tcc.getMode() == mode){
		if(tcc.getSecondResolver()  instanceof NonGenericSortResolver &&
		   tcc.getFirstResolver() instanceof GenericSortResolver){

		    GenericSortResolver first = (GenericSortResolver)tcc.getFirstResolver();
		    if(first.getGenericSort().equals(gen)){
			  Sort superType = ((NonGenericSortResolver)tcc.getSecondResolver()).getSort();   
			  if(inst.extendsTrans(superType) && mode == Mode.NOT_IS_SUBTYPE){
			     return false; 
			  }
			  if(!inst.extendsTrans(superType) && mode == Mode.IS_SUBTYPE){
			     return false; 
			  }
		    }
		    
		  
		
		}
		
	    }
	}
	return true;
    }
    
    
    /**
     * Returns whether the taclet has a "isReference"-condition.
     * 
     * @param s the sort according to the "isReference"-condition.
     * @return returns 0 if there is no "isReference"-condition, 
     * else a value greater than 0:<br>
     * - <code>FALSE</code>: the taclet has no "isReference"-condition 
     * according to the given sort s.<br>
     * - <code>NULL_LEGAL</code>: the taclet has a "isReference"-condition, 
     * where <code>null</code> is allowed.<br>
     * - <code>NULL_ILLEGAL</code>: the taclet has a "isRefernce"-condition,
     * where <code>null</code> is not allowed.
     */
    public int containsIsReferenceCondition(Sort s){
	for(TypeCondition cond : typeCondition){
	    GenericSortResolver res;
	    if(cond.getResolver() instanceof GenericSortResolver){
		    res = (GenericSortResolver)cond.getResolver();
		    if(res.getGenericSort().equals(s)){
			if(cond.getIsReference()){
			    if(cond.getNonNull()){return NULL_LEGAL;}
			  return NULL_ILLEGAL;
			}
			
		    }
	    }
		
	}
	
	
	return FALSE;
    }
    

    
    
    
    
    
    
}


