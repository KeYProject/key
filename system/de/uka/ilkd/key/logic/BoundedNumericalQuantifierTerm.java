package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.BoundedNumericalQuantifier;

/**
 * Represents a term with a numerical quantifier as top level operator.
 * 
 * This kind of terms bind variables in their third sub term, while the first
 * two ones express range restrictions.
 */
class BoundedNumericalQuantifierTerm extends OpTerm.ArbitraryOpTerm {

    private final ArrayOfQuantifiableVariable varsBoundHere;

    BoundedNumericalQuantifierTerm(BoundedNumericalQuantifier op, Term[] subTerm, 
            ArrayOfQuantifiableVariable varsBoundHere) {
        super(op, subTerm);
	this.varsBoundHere = varsBoundHere;
    }

    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
	return n == 2 ? varsBoundHere : EMPTY_VAR_LIST;
    }
}
