// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.op.BoundedNumericalQuantifier;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * Represents a term with a numerical quantifier as top level operator.
 * 
 * This kind of terms bind variables in their third sub term, while the first
 * two ones express range restrictions.
 */
class BoundedNumericalQuantifierTerm extends OpTerm.ArbitraryOpTerm {

    private final ImmutableArray<QuantifiableVariable> varsBoundHere;

    BoundedNumericalQuantifierTerm(BoundedNumericalQuantifier op, Term[] subTerm, 
				   ImmutableArray<QuantifiableVariable> varsBoundHere) {
        super(op, subTerm);
	this.varsBoundHere = varsBoundHere;
    }

    public ImmutableArray<QuantifiableVariable> varsBoundHere(int n) {
	return n == 2 ? varsBoundHere : EMPTY_VAR_LIST;
    }
}
