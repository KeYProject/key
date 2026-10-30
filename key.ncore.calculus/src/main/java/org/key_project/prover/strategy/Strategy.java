/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy;

import org.key_project.logic.Named;
import org.key_project.prover.indexing.RuleAppIndexMode;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;



/**
 * Generic interface for evaluating the cost of a RuleApp with regard to a specific strategy
 */
public interface Strategy<Goal extends ProofGoal<@NonNull Goal>> extends Named, Feature {
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
    default RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return computeCost(app, pos, goal, new MutableState());
    }

    /**
     * Checks if the {@link Strategy} should stop at the first non-closeable {@link Goal}.
     *
     * @return {@code true} stop, {@code false} continue on other {@link Goal}s.
     */
    boolean isStopAtFirstNonCloseableGoal();

    /**
     * Returns the mode of the rule app indices (automatic or interactive) required for the
     * strategy.
     * Usually (and by default) the index to be used is the automatic index
     * {@link RuleAppIndexMode#AUTO}. Some strategies/macros require the
     * interactive index as they apply rules without an attached heuristic.
     *
     * @return the mode specifying which index to use
     */
    default RuleAppIndexMode getRuleAppIndexMode() {
        return RuleAppIndexMode.AUTO;
    }

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

    boolean isResponsibleFor(RuleSet rs);

    default RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio,
            Goal goal, MutableState mState) {
        return TopRuleAppCost.INSTANCE;
    }
}
