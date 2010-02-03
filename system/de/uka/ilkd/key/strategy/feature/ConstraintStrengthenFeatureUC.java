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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.ConstraintTableModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * This feature is similar to <code>ConstraintStrengthenFeature</code>, but
 * instead of just comparing the constraint resulting from a rule application
 * with the original constraint of the find-formula of the application, the new
 * constraint is compared with the joint of the original constraint and the user
 * constraint. I.e. the feature returns zero iff the new constraint is stronger
 * than <code>userConstraint.join(formulaConstraint)</code>.
 */
public class ConstraintStrengthenFeatureUC extends
                                        AbstractConstraintStrengthenFeature {

    private final ConstraintTableModel userConstraint;
    
    private ConstraintStrengthenFeatureUC (ConstraintTableModel userConstraint) {
        this.userConstraint = userConstraint;
    }

    public static Feature create (Proof proof) {
        return new ConstraintStrengthenFeatureUC ( proof.getUserConstraint () );
    }
    
    protected boolean filter (TacletApp app, PosInOccurrence pos, Goal goal) {
        if ( app.constraint ().isBottom () ) return false;
        
        final Services services = goal.proof().getServices();
        final Constraint formulaConstraint;
        if ( pos == null ) {
            // there is no find-part, we are instead using constraints of the
            // if-formulas
            if ( app.ifInstsComplete () ) {
                formulaConstraint = getIfConstraint ( app, services );
            } else {
                return false;
            }
        } else {
            formulaConstraint = pos.constrainedFormula ().constraint ();
        }

        final Constraint uc = userConstraint.getConstraint ();
        if ( formulaConstraint.isBottom () && uc.isBottom () ) return true;
        
        final Constraint oriConstraint = formulaConstraint.join ( uc, services );
        return !oriConstraint.isAsStrongAs ( app.constraint () );
    }

}
