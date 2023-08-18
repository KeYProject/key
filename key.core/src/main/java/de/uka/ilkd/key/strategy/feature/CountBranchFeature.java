/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Feature that returns the number of branches for a given taclet application Size of "assumes"
 * sequents is currently not considered
 */
public class CountBranchFeature implements Feature {

    public static final Feature INSTANCE = new CountBranchFeature();

    private CountBranchFeature() {
    }

    /**
     * Compute the cost of a RuleApp.
     *
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @return the cost of <code>app</code>
     */
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        if (app.rule() instanceof Taclet) {
            final Taclet tac = (Taclet) app.rule();
            final long branches = tac.goalTemplates().size();
            return NumberRuleAppCost.create(branches);
        }
        return NumberRuleAppCost.getZeroCost();
    }
}
