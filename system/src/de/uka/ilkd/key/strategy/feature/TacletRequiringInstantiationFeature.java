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

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.SchemaVariable;
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
        final ImmutableSet<SchemaVariable> neededVars = app.uninstantiatedVars ();
        final ImmutableSet<SchemaVariable> ifFindVars = app.taclet ().getIfFindVariables ();
        for (SchemaVariable neededVar : neededVars) {
            if (!ifFindVars.contains(neededVar)) return true;
        }
        return false;
    }
}