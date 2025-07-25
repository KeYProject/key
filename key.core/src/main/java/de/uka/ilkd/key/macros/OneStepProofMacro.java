/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;

/**
 * Apply a single proof step.
 *
 * @author Simon Greiner
 */
public class OneStepProofMacro extends StrategyProofMacro {

    @Override
    public String getName() {
        return "One Single Proof Step";
    }

    @Override
    public String getScriptCommandName() {
        return "onestep";
    }

    @Override
    public String getCategory() {
        return "Simplification";
    }

    @Override
    public String getDescription() {
        return "One single proof step is applied";
    }

    @Override
    protected Strategy<@NonNull Goal> createStrategy(Proof proof,
            PosInOccurrence posInOcc) {
        return new OneStepStrategy(proof.getActiveStrategy());
    }


    /**
     * Strategy with counter, s.t. only one rule is applied
     *
     *
     */

    private static class OneStepStrategy implements Strategy<@NonNull Goal> {

        private static final Name NAME = new Name(OneStepStrategy.class.getSimpleName());
        private int counter;
        public final Strategy<@NonNull Goal> delegate;

        public OneStepStrategy(Strategy<@NonNull Goal> delegate) {
            this.delegate = delegate;
            this.counter = 0;
        }

        @Override
        public Name name() {
            return NAME;
        }

        /**
         * If no rule was applied yet, apply the first rule and increase counter, s.t. no more rules
         * can be applied.
         */
        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio,
                Goal goal) {
            if (counter == 0 && delegate.isApprovedApp(app, pio, goal)) {
                counter++;
                return true;
            } else {
                return false;
            }
        }

        @Override
        public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
                PosInOccurrence pio, Goal goal,
                MutableState mState) {
            return delegate.computeCost(app, pio, goal, mState);

        }


        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
            delegate.instantiateApp(app, pio, goal, collector);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }
}
