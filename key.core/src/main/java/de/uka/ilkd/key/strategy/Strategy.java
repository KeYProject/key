/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.feature.Feature;

/**
 * Generic interface for evaluating the cost of a RuleApp with regard to a specific strategy
 */
public interface Strategy extends Named, Feature {
    /**
     * Checks if the {@link Strategy} should stop at the first non closeable {@link Goal}.
     *
     * @return {@code true} stop, {@code false} continue on other {@link Goal}s.
     */
    boolean isStopAtFirstNonCloseableGoal();

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is called immediately before a rule is really
     * applied
     *
     * @return true iff the rule should be applied, false otherwise
     */
    boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal);

    /**
     * Instantiate an incomplete <code>RuleApp</code>. This method is called when the
     * <code>AutomatedRuleApplicationManager</code> comes across a rule application in which some
     * schema variables are not yet instantiated, or which is in some other way incomplete. The
     * strategy then has the opportunity to return/provide a list of (more) complete rule
     * applications by feeding them into the provided <code>RuleAppCostCollector</code>.
     */
    void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            RuleAppCostCollector collector);

    /**
     * Updates the {@link Strategy} for the given {@link Proof} by setting the {@link Strategy}'s
     * {@link StrategyProperties} to the given ones.
     *
     * @param proof The {@link Proof} the strategy of which should be updated.
     * @param p The new {@link StrategyProperties}
     */
    static void updateStrategySettings(Proof proof, StrategyProperties p) {
        final Strategy strategy = proof.getActiveStrategy();
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setStrategy(strategy.name());
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(p);

        proof.getSettings().getStrategySettings().setStrategy(strategy.name());
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(p);

        proof.setActiveStrategy(strategy);
    }
}
