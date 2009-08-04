// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;



public class MemberPVToField extends AbstractMetaOperator {
    
    private static final TermBuilder TB = TermBuilder.DF;
    

    public MemberPVToField() {
        super(new Name("#memberPVToField"), 1);
    }
    

    @Override
    public Term calculate(Term term, 
	    		  SVInstantiations svInst, 
	    		  Services services ) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        
        ProgramVariable fieldPV = (ProgramVariable) term.sub(0).op();        
        Function fieldSymbol = heapLDT.getFieldSymbolForPV(fieldPV, services);
        return TB.func(fieldSymbol);
    }
}
