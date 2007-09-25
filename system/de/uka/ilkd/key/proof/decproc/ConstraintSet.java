// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;



/**
 * A class representing a set of Constraints from which 
 * partial sets can be chosen
 */
public class ConstraintSet {
    protected Vector constrainedFormulas;
    protected Constraint userConstraint;
    protected HashSet usedConstrainedFormulas;
    protected Constraint chosenConstraint;

    /**
     * Creates a new ConstraintSet whith the goal's constraints
     * @param g The goal the constraints should be taken from
     * @param userConstraint the Constraint the user entered
     */
    public ConstraintSet(Goal g, Constraint userConstraint) {
	constrainedFormulas = collectConstraints(g);
	usedConstrainedFormulas = new HashSet();
	chosenConstraint = Constraint.BOTTOM;
	this.userConstraint = userConstraint;
    }

    public ConstraintSet(Sequent s, Constraint userConstraint) {
	constrainedFormulas = collectConstraints(s);
	usedConstrainedFormulas = new HashSet();
	chosenConstraint = Constraint.BOTTOM;
	this.userConstraint = userConstraint;
    }

    /**
     * Return a collection of the goal's sequents' Constraints.
     * @return a collection of the goal's sequents' Constraints
     * @param g The goal which's sequent's Constraints should 
     * get collected
     */
    protected Vector collectConstraints(Goal g) {
	return collectConstraints(g.sequent());
    }

    /**
     * Return a collection of the Sequents' Constraints.
     * @return a collection of the Sequents' Constraints
     * @param s The sequent from which the Constraints should 
     * get collected
     */
    protected Vector collectConstraints(Sequent s) {
	Vector vec = new Vector();
	vec = collectConstraints(s.antecedent());
	vec.addAll(collectConstraints(s.succedent()));
	return vec;
    }

    /**
     * Return a collection of the Semisequents' Constraints.
     * @return a collection of the Semisequents' Constraints
     * @param g The SemiSequent from which the Constraints should 
     * get collected
     */
    protected Vector collectConstraints(Semisequent g) {
	Vector vec = new Vector();
	for (int i = 0; i < g.size(); i++) {
	    vec.add(g.get(i));
	}
	return vec;
    }

    /**
     * Returns wether the parameter cf's Constraint was used 
     * to build the Constraint returned with the last call 
     * of chooseConstraint().
     * @param cf The constrained formula to check.
     * @returns true if cf was put into the to set, no otherwise.
     **/
    public boolean used(ConstrainedFormula cf) {
	return usedConstrainedFormulas.contains(cf);
    }

    /**
     * Returns the Constraint generated with the last call 
     * of chooseConstraint().
     * @returns the Constraint generated with the last call 
     * of chooseConstraint().
     */
    public Constraint chosenConstraint() {
	return this.chosenConstraint;
    }

    /**
     * Adds a user Constraint to the current chosenConstraint.
     * The philosophy behind this approach is that the decision 
     * procedure is always called without the user Constraints 
     * first, and the call is not handled by this class.
     * If the new generated Constraint is not satisfiable, the 
     * user Constraint is added nevertheless. The caller should 
     * avoid calling the decision procedure afterwards.
     *
     * @returns Wether the new Constraint is satisfiable or not
     * @param p_userConstraint As the name implies, this is the 
     * user Constraint.
     */
    public boolean addUserConstraint(Constraint p_userConstraint) {
	chosenConstraint = chosenConstraint.join(p_userConstraint, null);
	return chosenConstraint.isSatisfiable();
    }

    /**
     * Chooses a new set of Constraints
     * This method has (should/will have) a state, 
     * uses the attributes of 'this' to remember its state.
     * This is not implemented yet. And it is likely that it will 
     * stay this way for a while.
     * @returns A set of constraints joined to form one.
     *    It tries (using a simple heuristic) to find a maximum consistent
     *    consistent subset of all collected constraints.
     *    It remembers whose ConstrainedFormula's constraints were used.
     */
    public Constraint chooseConstraintSet() {
	Constraint tempConstraint;
	Constraint usedConstraint = Constraint.BOTTOM;
	//System.out.println("Amount of Constraints to choose: "+
	//constraints.size());
	Iterator i;
	for ( i = constrainedFormulas.iterator(); i.hasNext(); ) {
 	    ConstrainedFormula next = (ConstrainedFormula)i.next();
	    //System.out.println("Next Constrait:     " + next.constraint());
	    if (next.constraint().isSatisfiable()) {
		tempConstraint = usedConstraint.join(next.constraint(), null);
		//System.out.println("Combined: " + tempConstraint);
		if (tempConstraint.isSatisfiable()) {
		    usedConstraint = tempConstraint;
		    this.usedConstrainedFormulas.add(next);
		}
	    }
	}
	this.chosenConstraint = usedConstraint;
	return usedConstraint;
    }
    
}
