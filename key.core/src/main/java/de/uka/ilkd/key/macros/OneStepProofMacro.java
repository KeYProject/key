/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;

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
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new OneStepStrategy(proof.getActiveStrategy());
    }


    /**
     * Strategy with counter, s.t. only one rule is applied
     *
     *
     */

    private static class OneStepStrategy implements Strategy {

        private static final Name NAME = new Name(OneStepStrategy.class.getSimpleName());
        private int counter;
        public final Strategy delegate;

        public OneStepStrategy(Strategy delegate) {
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
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if (counter == 0 && delegate.isApprovedApp(app, pio, goal)) {
                counter++;
                return true;
            } else {
                return false;
            }
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
            return delegate.computeCost(app, pio, goal);

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
