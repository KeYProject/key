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

package de.uka.ilkd.key.rule.conditions;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Pair;


public final class DropEffectlessStoresCondition implements VariableCondition {
    private final TermSV h;
    private final TermSV o;
    private final TermSV f;
    private final TermSV x;
    private final TermSV result;
    
    public DropEffectlessStoresCondition(TermSV h,
	    				 TermSV o,
	    				 TermSV f,
	    				 TermSV x,	    				 
	    				 TermSV result) {
	this.h = h;
	this.o = o;
	this.f = f;
	this.x = x;
	this.result = result;
    }
    
    
    private static Term dropEffectlessStoresHelper(
	    		Term heapTerm, 
	    		TermServices services,
	    		ImmutableSet<Pair<Term,Term>> overwrittenLocs,
	    		Function store) {
	if(heapTerm.op() == store) {
	    final Term subHeapTerm  = heapTerm.sub(0);	    
	    final Term objTerm      = heapTerm.sub(1);
	    final Term fieldTerm    = heapTerm.sub(2);
	    final Term valueTerm    = heapTerm.sub(3);
	    final Pair<Term,Term> loc = new Pair<Term,Term>(objTerm, fieldTerm);
	    final Term newSubHeapTerm 
	    	= dropEffectlessStoresHelper(subHeapTerm, 
				             services, 
		    			     overwrittenLocs.add(loc), 
		    			     store);
	    if(overwrittenLocs.contains(loc)) {
		return newSubHeapTerm == null ? subHeapTerm : newSubHeapTerm;
	    } else {
		return newSubHeapTerm == null 
		       ? null 
                       : services.getTermBuilder().store(newSubHeapTerm, 
                	       	  objTerm, 
                	       	  fieldTerm, 
                	       	  valueTerm);
	    }
	} else {
	    return null;
	}
    }    
    
    
    private static Term dropEffectlessStores(Term t, Services services) {
	HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	assert t.sort() == heapLDT.targetSort();
	return dropEffectlessStoresHelper(
				t, 
				services, 
				DefaultImmutableSet.<Pair<Term,Term>>nil(), 
				heapLDT.getStore());
    }
    
    
    @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {	
	SVInstantiations svInst = mc.getInstantiations();
	Term hInst      = (Term) svInst.getInstantiation(h);
	Term oInst      = (Term) svInst.getInstantiation(o);
	Term fInst      = (Term) svInst.getInstantiation(f);
	Term xInst      = (Term) svInst.getInstantiation(x);
	Term resultInst = (Term) svInst.getInstantiation(result);
	if(hInst == null || oInst == null || fInst == null || xInst == null) {
	    return mc;
	}
	
	final Term properResultInst 
		= dropEffectlessStores(services.getTermBuilder().store(hInst, 
						oInst,
						fInst, 
						xInst), 
				       services);
	if(properResultInst == null) {
	    return null;
	} else if(resultInst == null) {
	    svInst = svInst.add(result, properResultInst, services);
	    return mc.setInstantiations(svInst);
	} else if(resultInst.equals(properResultInst)) {
	    return mc;
	} else {
	    return null;
	}
    }
    
    
    @Override
    public String toString () {
        return "\\dropEffectlessStores(" 
               + h + ", " + o + ", " + f + ", " + x + ", " + result + ")";
    }
}