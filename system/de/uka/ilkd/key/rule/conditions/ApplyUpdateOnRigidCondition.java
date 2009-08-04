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
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class ApplyUpdateOnRigidCondition implements VariableCondition {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final UpdateSV u;
    private final SchemaVariable x;
    private final SchemaVariable x2;
    
    public ApplyUpdateOnRigidCondition(UpdateSV u,
	                               SchemaVariable x,
	                               SchemaVariable x2) {
	this.u = u;
	this.x = x;
	this.x2 = x2;
    }
    
    
    private static Term applyUpdateOnRigid(Term update, Term target) {
	Term[] updatedSubs = new Term[target.arity()];
	for(int i = 0; i < updatedSubs.length; i++) {
	    updatedSubs[i] = TB.apply(update, target.sub(i));
	}
	Term result = TB.tf().createTerm(target.op(), 
				         updatedSubs,
				         target.boundVars(), 
				         target.javaBlock());
	return result;
    }
    
    
    @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	Term uInst  = (Term) svInst.getInstantiation(u);
	Term xInst  = (Term) svInst.getInstantiation(x);
	Term x2Inst = (Term) svInst.getInstantiation(x2);
	if(uInst == null || xInst == null) {
	    return mc;
	}
	
	if(!xInst.op().isRigid() || xInst.op().arity() == 0) {
	    return null;
	}
	
	Term properX2Inst = applyUpdateOnRigid(uInst, xInst);
	if(x2Inst == null) {
	    svInst = svInst.add(x2, properX2Inst);
	    return mc.setInstantiations(svInst);
	} else if(x2Inst.equals(properX2Inst)) {
	    return mc;
	} else {
	    return null;
	}
    }
    
    
    @Override
    public String toString () {
        return "\\applyUpdateOnRigid(" + u + ", " + x + ", " + x2 + ")";
    }
}
