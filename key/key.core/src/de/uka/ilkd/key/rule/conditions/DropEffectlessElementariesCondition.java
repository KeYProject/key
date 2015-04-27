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

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class DropEffectlessElementariesCondition 
						implements VariableCondition {
    private final UpdateSV u;
    private final SchemaVariable x;
    private final SchemaVariable result;
    
    public DropEffectlessElementariesCondition(UpdateSV u,
	                               	       SchemaVariable x,
	                               	       SchemaVariable x2) {
	this.u = u;
	this.x = x;
	this.result = x2;
    }
    
    
    private static Term dropEffectlessElementariesHelper(
	    				Term update, 
	    				Set<LocationVariable> relevantVars, TermServices services) {
	if(update.op() instanceof ElementaryUpdate) {
	    ElementaryUpdate eu = (ElementaryUpdate) update.op();
	    LocationVariable lhs = (LocationVariable) eu.lhs();
	    if(relevantVars.contains(lhs)) {
	        relevantVars.remove(lhs);
	        // removed, see bug #1269 (MU, CS)
//	        // updates of the form "x:=x" can be discarded (MU,CS)
//	        if(lhs.equals(update.sub(0).op())) {
//	            return TB.skip();
//	        }
		return null;
	    } else {
		return services.getTermBuilder().skip();
	    }
	} else if(update.op() == UpdateJunctor.PARALLEL_UPDATE) {
	    Term sub0 = update.sub(0);
            Term sub1 = update.sub(1);
            // first descend to the second sub-update to keep relevantVars in
            // good order
	    Term newSub1 = dropEffectlessElementariesHelper(sub1, relevantVars, services);
	    Term newSub0 = dropEffectlessElementariesHelper(sub0, relevantVars, services);
	    if(newSub0 == null && newSub1 == null) {
		return null;
	    } else {
		newSub0 = newSub0 == null ? sub0 : newSub0;
		newSub1 = newSub1 == null ? sub1 : newSub1;
		return services.getTermBuilder().parallel(newSub0, newSub1);
	    }
	} else if(update.op() == UpdateApplication.UPDATE_APPLICATION) {
	    Term sub0 = update.sub(0);
	    Term sub1 = update.sub(1);
	    Term newSub1 = dropEffectlessElementariesHelper(sub1, relevantVars, services);
	    return newSub1 == null ? null : services.getTermBuilder().apply(sub0, newSub1, null);
	} else {
	    return null;
	}
    }    
    
    
    private static Term dropEffectlessElementaries(Term update, 
	    					   Term target,
	    					   Services services) {
	TermProgramVariableCollector collector 
		= services.getFactory().create(services);
	target.execPostOrder(collector);
	Set<LocationVariable> varsInTarget = collector.result();
	Term simplifiedUpdate = dropEffectlessElementariesHelper(update, 
							         varsInTarget, services); 
	return simplifiedUpdate == null 
	       ? null 
	       : services.getTermBuilder().apply(simplifiedUpdate, target, null); 
    }
    
    


   @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	Term uInst      = (Term) svInst.getInstantiation(u);
	Term xInst      = (Term) svInst.getInstantiation(x);
	Term resultInst = (Term) svInst.getInstantiation(result);
	if(uInst == null || xInst == null) {
	    return mc;
	}
	
	Term properResultInst = dropEffectlessElementaries(uInst, 
						           xInst, 
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
        return "\\dropEffectlessElementaries(" 
               + u + ", " + x + ", " + result + ")";
    }
}