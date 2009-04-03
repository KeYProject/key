// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.explicitheap.ExplicitHeapConverter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class CastToSortOfField extends AbstractMetaOperator {

    private static final TermBuilder TB = TermBuilder.DF;

    public CastToSortOfField() {
        super(new Name("#castToSortOfField"), 2);
    }

    
    public boolean validTopLevel(Term term) {
        return  term.arity()==arity();
    }

    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        Term fieldTerm = term.sub(0);
        Term subTerm   = term.sub(1);
        assert fieldTerm.sort() == services.getJavaInfo().getFieldSort();
        
        Sort sort = ExplicitHeapConverter.INSTANCE.getSortOfField((Function)fieldTerm.op(), services);
        return TB.tf().createCastTerm((AbstractSort) sort, subTerm);
    }
    
}
