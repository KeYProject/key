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
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class InsertConstantValueCondition implements VariableCondition {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private TermSV f;
    private TermSV result;
    
    public InsertConstantValueCondition(TermSV f, TermSV result) {
	this.f = f;
	this.result = result;
    }
    
    
    private static Term getConstantValue(Function fieldSymbol, 
	    			         Services services) {
	HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	ProgramVariable fieldPV = heapLDT.getPVForFieldSymbol(fieldSymbol, 
							      services);
	if(fieldPV instanceof ProgramConstant) {
	    Literal lit = ((ProgramConstant)fieldPV).getCompileTimeConstant();
	    return services.getTypeConverter().convertToLogicElement(lit);
	} else {
	    return null;
	}
    }
    
    
    @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	if(var == f) {
	    Term inst = (Term) instCandidate;
	    if(!(inst.op() instanceof Function)) {
		return null;
	    }
	    Term constant = getConstantValue((Function)inst.op(), 
		    			     services);
	    if(constant == null) {
		return null;
	    } else {
		return mc.setInstantiations(svInst.add(result, 
						       constant, 
						       services));
	    }
	} else {
	    return mc;
	}
    }
    
    
    @Override
    public String toString () {
        return "\\insertConstantValue(" + f + ", " + result + ")";
    }
}
