// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Abstract superclass for features of TacletApps that have either zero or top
 * cost.
 */
public abstract class BinaryTacletAppFeature extends BinaryFeature {
    
    private final boolean nonTacletValue;

    protected BinaryTacletAppFeature () {
        nonTacletValue = true;
    }

    /**
     * @param p_nonTacletValue
     *            the value that is to be returned should the feature be applied
     *            to a rule that is not a taclet
     */
    protected BinaryTacletAppFeature ( boolean p_nonTacletValue ) {
        nonTacletValue = p_nonTacletValue;
    }

    final protected boolean filter ( RuleApp app, PosInOccurrence pos, Goal goal ) {
        if ( app instanceof TacletApp )
            return filter ( (TacletApp)app, pos, goal );
        return nonTacletValue;
    }
    
    /**
     * Compute whether the result of the feature is zero (<code>true</code>)
     * or infinity (<code>false</code>)
     * 
     * @param app
     *            the TacletApp
     * @param pos
     *            position where <code>app</code> is to be applied
     * @param goal
     *            the goal on which <code>app</code> is to be applied
     * @return true iff the the result of the feature is supposed to be zero.
     */
    protected abstract boolean filter ( TacletApp app,
                                        PosInOccurrence pos,
                                        Goal goal );
}
