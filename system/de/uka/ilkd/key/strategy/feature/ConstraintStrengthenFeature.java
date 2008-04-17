// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * A binary feature that returns zero iff the constraint of the given taclet app
 * is stronger than the original constraint of the formula to which the rule is
 * applied (i.e. replacewith-clauses are changed into add-clauses). For taclets
 * that do not have a find-clause, the app constraint is compared with the
 * conjunction of the constraints attached to matched if-formulas.
 */
public class ConstraintStrengthenFeature extends AbstractConstraintStrengthenFeature {

    public final static Feature INSTANCE = new ConstraintStrengthenFeature (); 
    
    private ConstraintStrengthenFeature () {}
    
    protected boolean filter (TacletApp app, PosInOccurrence pos, Goal goal) {
        final Constraint formulaConstraint;
        if ( pos == null ) {
            // there is no find-part, we are instead using constraints of the
            // if-formulas
            if ( app.ifInstsComplete () ) {
                formulaConstraint = getIfConstraint ( app, 
                        goal.proof().getServices() );
            } else {
                return false;
            }
        } else {
            formulaConstraint = pos.constrainedFormula ().constraint ();
        }
        
        return !formulaConstraint.isAsStrongAs ( app.constraint () );
    }

}
