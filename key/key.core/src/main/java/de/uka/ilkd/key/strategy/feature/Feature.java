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
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * A {@link Feature} is a class that is able to compute the cost of a
 * {@link RuleApp}.
 */
public interface Feature {

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     *
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @return the cost of the rule application expressed as a
     * <code>RuleAppCost</code> object. <code>TopRuleAppCost.INSTANCE</code>
     * indicates that the rule shall not be applied at all (it is discarded by
     * the strategy).
     */
    RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal);
}
