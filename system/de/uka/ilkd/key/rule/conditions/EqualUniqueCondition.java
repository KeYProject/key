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
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class EqualUniqueCondition implements VariableCondition {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final TermSV t;
    private final TermSV t2;
    private final FormulaSV phi;
    
    
    public EqualUniqueCondition(TermSV t, TermSV t2, FormulaSV phi) {
        this.t = t;
        this.t2 = t2;
        this.phi = phi;
    }
    
    
    private static Term equalUnique(Term t1, Term t2, Services services) {
	if(!(t1.op() instanceof Function 
	     && t2.op() instanceof Function
	     && ((Function)t1.op()).isUnique()
	     && ((Function)t2.op()).isUnique())) {
	    return null;
	} else if(t1.op() == t2.op()) {
	    Term result = TB.tt();
	    for(int i = 0, n = t1.arity(); i < n; i++) {
		result = TB.and(result, TB.equals(t1.sub(i), t2.sub(i)));
	    }
	    return result;
	} else {
	    return TB.ff();
	}
    }
    
    
    @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	Term tInst   = (Term) svInst.getInstantiation(t);
	Term t2Inst  = (Term) svInst.getInstantiation(t2);
	Term phiInst = (Term) svInst.getInstantiation(phi);
	if(tInst == null || t2Inst == null) {
	    return mc;
	}
	
	Term properPhiInst = equalUnique(tInst, t2Inst, services);
	if(properPhiInst == null) {
	    return null;
	} else if(phiInst == null) {
	    svInst = svInst.add(phi, properPhiInst);
	    return mc.setInstantiations(svInst);
	} else if(phiInst.equals(properPhiInst)) {
	    return mc;
	} else {
	    return null;
	}
    }
    

    @Override
    public String toString () {
        return "\\equalUnique (" + t + ", " + t2 + ", " + phi + ")";
    }
}
