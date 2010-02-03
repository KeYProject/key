// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Feature that returns zero if there is no atom with negative polarity on a
 * common d-path and on the left of the find-position within the find-formula as
 * a formula of the antecedent. Used terminology is defined in Diss. by Martin
 * Giese.
 */
public class LeftmostNegAtomFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new LeftmostNegAtomFeature ();

    private LeftmostNegAtomFeature () {}
    
    protected RuleAppCost doComputation (PosInOccurrence pos, Term findTerm) {
        final PIOPathIterator it = pos.iterator ();
        boolean positive = pos.isInAntec ();

        while ( it.next () != -1 ) {
            final Term subTerm = it.getSubTerm ();
            final Operator op = subTerm.op ();

            if ( it.getChild () == 0 ) {
                if ( op == Op.NOT || op == Op.IMP )
                    positive = !positive;
                else if ( op == Op.EQV )
		    return BinaryFeature.ZERO_COST; // TODO

                continue;
            }

            if ( op == ( positive ? Op.OR : Op.AND ) ) {
                if ( containsNegAtom ( subTerm.sub ( 0 ), positive ) )
		    return BinaryFeature.TOP_COST;
            } else if ( positive && op == Op.IMP ) {
                if ( containsNegAtom ( subTerm.sub ( 0 ), false ) )
		    return BinaryFeature.TOP_COST;
            } else if ( op == Op.EQV )
		return BinaryFeature.ZERO_COST; // TODO
        }

        return BinaryFeature.ZERO_COST;
    }

}
