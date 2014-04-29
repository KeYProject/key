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

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * Abstract superclass for features that have either zero cost or top cost.
 */
public abstract class BinaryFeature implements Feature {

    protected BinaryFeature () {}
    
    /** Constant that represents the boolean value true */
    public static final RuleAppCost ZERO_COST = NumberRuleAppCost.getZeroCost();
    /** Constant that represents the boolean value false */
    public static final RuleAppCost TOP_COST  = TopRuleAppCost.INSTANCE;
    
    public RuleAppCost compute ( RuleApp app, PosInOccurrence pos, Goal goal ) {
        return filter ( app, pos, goal ) ? ZERO_COST : TOP_COST; 
    }
    
    /**
     * Compute whether the result of the feature is zero (<code>true</code>)
     * or infinity (<code>false</code>)
     * 
     * @param app
     *            the RuleApp
     * @param pos
     *            position where <code>app</code> is to be applied
     * @param goal
     *            the goal on which <code>app</code> is to be applied
     * @return true iff the the result of the feature is supposed to be zero.
     */
    protected abstract boolean filter ( RuleApp app,
                                        PosInOccurrence pos,
                                        Goal goal );

}