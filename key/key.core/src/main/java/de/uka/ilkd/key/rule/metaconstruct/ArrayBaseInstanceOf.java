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

/*
 * Created on Apr 14, 2005
 */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * Creates an <tt>Type::instance(..)</tt> term for the component type of the
 * array. The component type has to be a reference type.
 */
public final class ArrayBaseInstanceOf extends AbstractTermTransformer {

    public ArrayBaseInstanceOf() {
        super(new Name("#arrayBaseInstanceOf"), 2);
    }

    /**
     * returns an <tt>G::instance(term.sub(1))</tt> term for the element sort of 
     * the given array . It is assumed that <tt>term.sub(0)</tt> is either a term of 
     * reference array sort or a term with an <tt>exactInstance</tt> symbol as top level 
     * depending on a reference array sort.
     */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term array = term.sub(0);
        final Term element = term.sub(1);

        final Sort arraySort;
        if(array.op() instanceof SortDependingFunction
           && ((SortDependingFunction)array.op()).getKind().equals(Sort.EXACT_INSTANCE_NAME)) {
            arraySort = ((SortDependingFunction) array.op()).getSortDependingOn();
        } else {
            arraySort = array.sort();
        }

        assert arraySort instanceof ArraySort;

        final Sort arrayElementSort = ((ArraySort) arraySort).elementSort();

        Function instanceofSymbol
            =  arrayElementSort.getInstanceofSymbol(services);
        Debug.assertTrue(instanceofSymbol != null,
                "Instanceof symbol not found for ", arrayElementSort);
        
        return services.getTermFactory().createTerm(instanceofSymbol, element);
    }

}