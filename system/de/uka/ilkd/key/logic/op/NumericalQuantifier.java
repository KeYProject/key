package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Represents a numerical quantifier like <tt>\product</tt> or 
 * <tt>\sum</tt>. A numerical quantifier 
 */
public final class NumericalQuantifier extends AbstractOperator {

    /** the product operator */
    public static final NumericalQuantifier PRODUCT = new NumericalQuantifier(new Name("\\product"));
    
    /** the sum operator */
    public static final NumericalQuantifier SUM = new NumericalQuantifier(new Name("\\sum"));

    private NumericalQuantifier(Name name) {
        super(name, 2, new Boolean[]{true, true}, true);
    }

    @Override
    public Sort sort(ArrayOfTerm terms) {
        return terms.getTerm(1).sort ();
    }
    
    
    @Override
    protected boolean additionalValidTopLevel(Term term) {
        return term.sub(0).sort() == Sort.FORMULA; //TODO
    }
}
