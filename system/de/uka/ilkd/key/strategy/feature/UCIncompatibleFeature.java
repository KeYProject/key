// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.ConstraintTableModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * Feature that returns zero iff the constraint of concerned rule applications
 * is consistent with the chosen user constraint
 */
public class UCIncompatibleFeature extends BinaryTacletAppFeature {

    private final ConstraintTableModel userConstraint;
    
    private UCIncompatibleFeature (ConstraintTableModel userConstraint) {
        this.userConstraint = userConstraint;
    }

    public static Feature create (Proof proof) {
        return new UCIncompatibleFeature ( proof.getUserConstraint () );
    }

    protected boolean filter (TacletApp app, PosInOccurrence pos, Goal goal) {               
        return app.constraint ()
            .join ( userConstraint.getConstraint (), 
                    goal.proof().getServices() ).isSatisfiable ();
    }

}
