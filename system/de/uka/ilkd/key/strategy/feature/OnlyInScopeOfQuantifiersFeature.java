// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;


/**
 * BinaryFeature that return zero if all the operator is quantifier from root 
 * to position it point to.
 */
public class OnlyInScopeOfQuantifiersFeature extends BinaryTacletAppFeature {

    public final static Feature INSTANCE = new OnlyInScopeOfQuantifiersFeature ();

    private OnlyInScopeOfQuantifiersFeature() {}
    
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        Debug.assertFalse ( pos == null,
                            "Feature is only applicable to rules with find" );

        final PIOPathIterator it = pos.iterator ();
        while ( it.next () != -1 ) {
            final Term subterm = it.getSubTerm ();
            if ( ! ( subterm.op () instanceof Quantifier ) ) return false;
        }
        
        return true;
    }
}
