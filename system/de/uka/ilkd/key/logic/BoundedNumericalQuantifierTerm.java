package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.BoundedNumericalQuantifier;

class BoundedNumericalQuantifierTerm extends OpTerm.ArbitraryOpTerm {

    private ArrayOfQuantifiableVariable varsBoundHere;

    public BoundedNumericalQuantifierTerm(BoundedNumericalQuantifier op, Term[] subTerm, 
            ArrayOfQuantifiableVariable varsBoundHere) {
        super(op, subTerm);
	this.varsBoundHere = varsBoundHere;
    }

    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
	return n==2? varsBoundHere : EMPTY_VAR_LIST;
    }
    
}
