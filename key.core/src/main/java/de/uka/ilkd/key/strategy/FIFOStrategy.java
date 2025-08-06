/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;

/**
 * Trivial implementation of the Strategy interface that uses only the goal time to determine the
 * cost of a RuleApp.
 */
public class FIFOStrategy implements Strategy<Goal> {

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
    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pio,
            Goal goal,
            MutableState mState) {
        return NumberRuleAppCost.create(((de.uka.ilkd.key.proof.Goal) goal).getTime());
    }

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is called immediately before a rule is really
     * applied
     *
     * @return true iff the rule should be applied, false otherwise
     */
    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio,
            Goal goal) {
        return true;
    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            RuleAppCostCollector collector) {}

    @Override
    public Name name() {
        return NAME;
    }

    public static final Strategy<Goal> INSTANCE = new FIFOStrategy();

    public static class Factory implements StrategyFactory {
        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public Strategy<Goal> create(Proof proof, StrategyProperties properties) {
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
