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
import de.uka.ilkd.key.logic.op.Function;
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
        Function arr = services.getJavaInfo().getArrayField();
        
        if(fieldTerm0.op() == arr && fieldTerm1.op() == arr) {
            return TB.equals(fieldTerm0.sub(0), fieldTerm1.sub(0));
        } else if((fieldTerm0.op() == arr && fieldTerm1.arity() == 0)
                  || (fieldTerm0.arity() == 0 && fieldTerm1.op() == arr)) {
            return TB.ff();
        } else if(fieldTerm0.arity() == 0 
                  && fieldTerm1.arity() == 0 
                  && fieldTerm0.op() instanceof RigidFunction 
                  && fieldTerm1.op() instanceof RigidFunction) {
            if(fieldTerm0.op() ==  fieldTerm1.op()) {
                return TB.tt();
            } else {
                return TB.ff();
            }
        } else {
            return TB.equals(fieldTerm0, fieldTerm1);
        }
    }
    

    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
}
