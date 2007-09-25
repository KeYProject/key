/*
 * Created on Apr 14, 2005
 */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.ExactInstanceSymbol;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * Creates an <tt>Type::instance(..)</tt> term for the component type of the
 * array. The component type has to be a reference type.
 */
public class ArrayBaseInstanceOf extends AbstractMetaOperator {

    public ArrayBaseInstanceOf() {
        super(new Name("#arrayBaseInstanceOf"), 2);
    }

    /**
     * returns an <tt>G::instance(term.sub(1))</tt> term for the element sort of 
     * the given array . It is assumed that <tt>term.sub(0)</tt> is either a term of 
     * reference array sort or a term with an <tt>exactInstance</tt> symbol as top level 
     * depending on a reference array sort.
     */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        final Term array = term.sub(0);
        final Term element = term.sub(1);

        final Sort arraySort;
        if (array.op() instanceof ExactInstanceSymbol) {
            arraySort = ((ExactInstanceSymbol) array.op()).
            getSortDependingOn();
        } else {
            arraySort = array.sort();
        }

        assert arraySort instanceof ArraySort;

        final Sort arrayElementSort = ((ArraySort) arraySort).elementSort();

        Function instanceofSymbol = null;
        if (arrayElementSort instanceof SortDefiningSymbols) {
            assert arrayElementSort instanceof ArraySort || arrayElementSort instanceof ObjectSort;
            instanceofSymbol = (Function) ((SortDefiningSymbols) arrayElementSort)
                    .lookupSymbol(new Name("instance"));
        }
        Debug.assertTrue(instanceofSymbol != null,
                "Instanceof symbol not found for ", arrayElementSort);
        
        return TermFactory.DEFAULT.createFunctionTerm(instanceofSymbol, 
                element);
    }

}
