// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Term;



/** A void SimultaneousUpdateSimplifier to have a consistent
 * behaviour (i.e. failure) if asmkey attempts to use this
 * (per mistake).
 *
 * @author Stanislas Nanchen
 */

public class SimultaneousUpdateSimplifier
    extends de.uka.ilkd.key.rule.UpdateSimplifier {

    
    /** 
     * creates a new simplifier that makes use of simultaneous updates and the
     * DefaultDeletionStrategy 
     * 
     */
    public SimultaneousUpdateSimplifier() {
	super();
    }

    /**
     * creates a new simplifier 
     * @param deletionStrategy the DeletionStrategy to use 
     * @param useSimultaneousUpdates a boolean that allows the use of simultaneous
     * updates
     */
    /*public SimultaneousUpdateSimplifier(DeletionStrategy deletionStrategy,
					boolean useSimultaneousUpdates) {

	super(deletionStrategy, useSimultaneousUpdates);	
	}*/



    // static
    public static int depthWithoutUpdates(Term t) {
	//throw new RuntimeException("AsmKeY: SimultaneousUpdateSimplifier not implemented in AsmKeY.");
	return t.depth();
    }
    


    /**
     * Convenience method if only one update is applied.
     */
    public Term simplify(Term update, Term target) {
	//throw new RuntimeException("AsmKeY: SimultaneousUpdateSimplifier not implemented in AsmKeY.");
	return target;
    }

    /**
     * starts simplification
     */
    public Term simplify(Term target, int dummy) {
	//throw new RuntimeException("AsmKeY: SimultaneousUpdateSimplifier not implemented in AsmKeY.");
	return target;
    }

    /**
     * starts simplification
     */
    public Term simplify(Term target) {
	//throw new RuntimeException("AsmKeY: SimultaneousUpdateSimplifier not implemented in AsmKeY.");
	return target;
    }

    /**
     * starts simplification for a contrained formula
     */
    public ConstrainedFormula simplify(ConstrainedFormula target, 
				       Constraint userConstraint) {
	//throw new RuntimeException("AsmKeY: SimultaneousUpdateSimplifier not implemented in AsmKeY.");
	return target;
    }

    /**
     * void is asmkey
     */
    public int potentialAliased
	(Term fst, Term snd, boolean ignore) {
	//throw new RuntimeException("AsmKeY: SimultaneousUpdateSimplifier not implemented in AsmKeY.");
	return -1; //NOT ALIASED
    }


}

