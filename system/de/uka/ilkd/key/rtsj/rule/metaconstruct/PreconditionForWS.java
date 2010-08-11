// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rtsj.logic.op.WorkingSpaceRigidOp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class PreconditionForWS extends AbstractMetaOperator {

    public PreconditionForWS() {
        super(new Name("#getPreForWS"), 2);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return ((WorkingSpaceRigidOp) term.sub(0).op()).getPre((WorkingSpaceRigidOp) term.sub(1).op(), services);
    }
    
    public Sort sort(Term[] term){
        return Sort.FORMULA;
    }

}
