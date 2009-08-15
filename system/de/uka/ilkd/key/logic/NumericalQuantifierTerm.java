package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.op.NumericalQuantifier;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * Numerical quantifiers bind a variable in their first sub term
 * 
 * 
 * @see de.uka.ilkd.key.logic.op.NumericalQuantifier 
 * 
 */
class NumericalQuantifierTerm extends OpTerm.ArbitraryOpTerm {

    private final ImmutableArray<QuantifiableVariable> varsBoundHere;

    public NumericalQuantifierTerm(NumericalQuantifier op, Term[] subTerm, 
            ImmutableArray<QuantifiableVariable> varsBoundHere) {
        super(op, subTerm);
	this.varsBoundHere = varsBoundHere;
    }

    public ImmutableArray<QuantifiableVariable> varsBoundHere(int n) {
	return varsBoundHere;
    }
    
}
