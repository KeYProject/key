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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;



public final class MemberPVToField extends AbstractTermTransformer {  

    public MemberPVToField() {
        super(new Name("#memberPVToField"), 1);
    }
    

    @Override
    public Term transform(Term term, 
	    		  SVInstantiations svInst, 
	    		  Services services ) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();	
 	
 	    
 	Operator op = term.sub(0).op();
	if(op instanceof LocationVariable) {
	    LocationVariable fieldPV = (LocationVariable) term.sub(0).op();
	    Function fieldSymbol 
	    	= heapLDT.getFieldSymbolForPV(fieldPV, services);
	    return services.getTermBuilder().func(fieldSymbol);
	} else if(heapLDT.getSortOfSelect(op) != null) {
	    return term.sub(0).sub(2);
	} else {
	    assert false;
	    return null;
	}
    }
}