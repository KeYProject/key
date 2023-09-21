/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * A {@link Feature} is a class that is able to compute the cost of a {@link RuleApp}.
 */
public interface Feature {

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     *
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @return the cost of the rule application expressed as a <code>RuleAppCost</code> object.
     *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule shall not be applied at
     *         all (it is discarded by the strategy).
     */
    RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal);
}
