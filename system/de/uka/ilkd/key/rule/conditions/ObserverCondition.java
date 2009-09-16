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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class ObserverCondition implements VariableCondition {

    private final TermSV obs;
    private final TermSV heap;
    private final TermSV obj;
    
    
    public ObserverCondition(TermSV obs, TermSV heap, TermSV obj) {
        this.obs = obs;
        this.heap = heap;
        this.obj = obj;
    }

      
    @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	final Term obsInst  = (Term) svInst.getInstantiation(obs);
	final Term heapInst = (Term) svInst.getInstantiation(heap);
	if(obsInst == null || heapInst == null) {
	    return mc;
	}
	
	if(!(obsInst.op() instanceof ObserverFunction) 
	   || !obsInst.sub(0).equals(heapInst)) {
	    return null;
	}
	final ObserverFunction of = (ObserverFunction) obsInst.op();
	
	if(of.isStatic()) {
	    return null;//TODO
	}
	
	final Term objInst = (Term) svInst.getInstantiation(obj);
	final Term properObjInst = obsInst.sub(1);
	if(objInst == null) {
	    svInst = svInst.add(obj, properObjInst, services);
	    return mc.setInstantiations(svInst);
	} else if(objInst.equals(properObjInst)) {
	    return mc;
	} else {
	    return null;
	}
    }

    
    @Override
    public String toString () {
        return "\\isObserver (" + obs + ", " + heap + ", " + obj + ")";
    }
}
