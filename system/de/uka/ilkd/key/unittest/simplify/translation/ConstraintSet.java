// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest.simplify.translation;

import java.util.HashSet;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Constraint;

/**
 * A class representing a set of Constraints from which partial sets can be
 * chosen
 */
public class ConstraintSet {

    private HashSet<Constraint> usedConstrainedFormulas;

    private Constraint chosenConstraint;

    public ConstraintSet() {
	usedConstrainedFormulas = new HashSet<Constraint>();
	chosenConstraint = Constraint.BOTTOM;
    }

    /**
     * Adds a user Constraint to the current chosenConstraint. The philosophy
     * behind this approach is that the decision procedure is always called
     * without the user Constraints first, and the call is not handled by this
     * class. If the new generated Constraint is not satisfiable, the user
     * Constraint is added nevertheless. The caller should avoid calling the
     * decision procedure afterwards.
     * 
     * @returns Wether the new Constraint is satisfiable or not
     * @param p_userConstraint
     *            As the name implies, this is the user Constraint.
     */
    public boolean addUserConstraint(Constraint p_userConstraint) {
	chosenConstraint = chosenConstraint.join(p_userConstraint, null);
	return chosenConstraint.isSatisfiable();
    }

    /**
     * Returns the Constraint generated with the last call of
     * chooseConstraint().
     * 
     * @returns the Constraint generated with the last call of
     *          chooseConstraint().
     */
    public Constraint getChosenConstraint() {
	return chosenConstraint;
    }

    /**
     * Returns wether the parameter cf's Constraint was used to build the
     * Constraint returned with the last call of chooseConstraint().
     * 
     * @param cf
     *            The constrained formula to check.
     * @returns true if cf was put into the to set, no otherwise.
     **/
    public boolean used(ConstrainedFormula cf) {
	return usedConstrainedFormulas.contains(cf);
    }

}
