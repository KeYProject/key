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

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.IteratorOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SetOfSchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Feature that returns zero iff the given rule app is a taclet app that needs
 * explicit instantiation of schema variables (which has not been done yet)
 */
public class TacletRequiringInstantiationFeature extends BinaryTacletAppFeature {

    public final static Feature INSTANCE 
        = new TacletRequiringInstantiationFeature ();
    
    private TacletRequiringInstantiationFeature() {
        super ( false );
    }
    
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        final SetOfSchemaVariable neededVars = app.neededUninstantiatedVars ();
        final SetOfSchemaVariable ifFindVars = app.taclet ().getIfFindVariables ();
        final IteratorOfSchemaVariable it = neededVars.iterator ();
        while ( it.hasNext () ) {
            if ( !ifFindVars.contains ( it.next () ) ) return true;
        }
        return false;
    }
}
