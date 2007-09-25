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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.ListOfUpdatePair;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Binary feature that returns zero iff a certain Taclet app has not already
 * been performed
 */
public class NonDuplicateAppModPositionFeature extends NonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppModPositionFeature ();

    public boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        if ( !app.ifInstsComplete () ) {
            return true;
        }

        return !containsRuleApp ( goal.appliedRuleApps (), app, pos );
    }

    protected boolean comparePio(TacletApp newApp,
                                 TacletApp oldApp,
                                 PosInOccurrence newPio, PosInOccurrence oldPio) {
        final Term newFocus = newPio.subTerm ();
        final Term oldFocus = oldPio.subTerm ();
        if ( !newFocus.equals ( oldFocus ) ) return false;
        if ( newFocus.isRigid () ) return true;
        final ListOfUpdatePair oldUpdateContext =
            oldApp.instantiations ().getUpdateContext ();
        final ListOfUpdatePair newUpdateContext =
            newApp.instantiations ().getUpdateContext ();
        return oldUpdateContext.equals ( newUpdateContext );
    }

}
