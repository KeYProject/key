/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.Strategy;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;


/**
 * Generic interface for evaluating the cost of a RuleApp with regard to a specific strategy
 */
public interface JavaStrategy extends Strategy<Goal> {
    /**
     * Evaluate the cost of a <code>RuleApp</code>. Starts a new independent computation.
     *
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @return the cost of the rule application expressed as a
     *         <code>RuleAppCost</code> object. <code>TopRuleAppCost.INSTANCE</code>
     *         indicates that the rule shall not be applied at all (it is discarded by
     *         the strategy).
     */
    @Override
    default RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return computeCost(app, pos, goal, new MutableState());
    }

    /**
     * Updates the {@link JavaStrategy} for the given {@link Proof} by setting the
     * {@link JavaStrategy}'s
     * {@link StrategyProperties} to the given ones.
     *
     * @param proof The {@link Proof} the strategy of which should be updated.
     * @param p The new {@link StrategyProperties}
     */
    static void updateStrategySettings(Proof proof, StrategyProperties p) {
        final org.key_project.prover.strategy.Strategy<de.uka.ilkd.key.proof.Goal> strategy =
            proof.getActiveStrategy();
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setStrategy(strategy.name());
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(p);

        proof.getSettings().getStrategySettings().setStrategy(strategy.name());
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(p);

        proof.setActiveStrategy(strategy);
    }

    @Override
    default boolean isResponsibleFor(RuleSet rs) { return false; }

    @Override
    default RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio,
            Goal goal, MutableState mState) {
        return null;
    }
}
