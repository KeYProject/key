/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

/**
 * Trivial implementation of the Strategy interface that uses only the goal time to determine the
 * cost of a RuleApp.
 */
public class FIFOStrategy implements Strategy {

    private static final Name NAME = new Name("FIFO");

    private FIFOStrategy() {
    }

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     *
     * @return the cost of the rule application expressed as a <code>RuleAppCost</code> object.
     *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule shall not be applied at
     *         all (it is discarded by the strategy).
     */
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
        return NumberRuleAppCost.create(goal.getTime());
    }

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is called immediately before a rule is really
     * applied
     *
     * @return true iff the rule should be applied, false otherwise
     */
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return true;
    }

    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            RuleAppCostCollector collector) {}

    public Name name() {
        return NAME;
    }

    public static final Strategy INSTANCE = new FIFOStrategy();

    public static class Factory implements StrategyFactory {
        public Name name() {
            return NAME;
        }

        public Strategy create(Proof proof, StrategyProperties properties) {
            return INSTANCE;
        }

        @Override
        public StrategySettingsDefinition getSettingsDefinition() {
            return null;
        }
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

}
