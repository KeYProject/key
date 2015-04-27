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


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class ObserverCondition implements VariableCondition {

    private final TermSV obs;
    private final TermSV heap;
    
    
    public ObserverCondition(TermSV obs, TermSV heap) {
        this.obs = obs;
        this.heap = heap;
    }

      
    @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	final Term obsInst  = (Term) svInst.getInstantiation(obs);
	
	if(obsInst == null) {
	    return mc;
	} else if(!(obsInst.op() instanceof IObserverFunction)) { 
	    return null;
	} 
	
	final Term heapInst = (Term) svInst.getInstantiation(heap);
	final Term properHeapInst = obsInst.sub(0);
	if(heapInst == null) {
	    svInst = svInst.add(heap, properHeapInst, services);
	    return mc.setInstantiations(svInst);
	} else if(heapInst.equals(properHeapInst)) {
	    return mc;
	} else {
	    return null;
	}
    }

    
    @Override
    public String toString () {
        return "\\isObserver (" + obs + ", " + heap + ")";
    }
}