// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.explicitheap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class SameField extends AbstractMetaOperator {

    private static final TermBuilder TB = TermBuilder.DF;

    public SameField() {
        super(new Name("#sameField"), 2);
    }

    
    public boolean validTopLevel(Term term) {
        return  term.arity() == arity();
    }

    

    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        Term fieldTerm0 = term.sub(0);
        Term fieldTerm1 = term.sub(1);
        Operator fieldOp0 = fieldTerm0.op();
        Operator fieldOp1 = fieldTerm1.op();
        
        if(fieldOp0 instanceof RigidFunction 
           && fieldOp1 instanceof RigidFunction
           && ((RigidFunction)fieldOp0).isUnique()
           && ((RigidFunction)fieldOp1).isUnique()) {
            if(fieldOp0 == fieldOp1) {
                Term result = TB.tt();
                for(int i = 0, n = fieldTerm0.arity(); i < n; i++) {
                    result = TB.and(result, TB.equals(fieldTerm0.sub(i),                
                                                      fieldTerm1.sub(i)));
                }
                return result;
            } else {
                return TB.ff();
            }
        } else {
            return TB.equals(fieldTerm0, fieldTerm1);            
        }
    }
}
