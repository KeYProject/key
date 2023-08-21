/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppFeature;

/**
 * Trivial implementation of the Strategy interface that uses only the goal time to determine the
 * cost of a RuleApp. A TacletFilter is used to filter out RuleApps.
 */
public class SimpleFilteredStrategy implements Strategy {

    private static final Name NAME = new Name("Simple ruleset");

    private final RuleFilter ruleFilter;

    private static final long IF_NOT_MATCHED_MALUS = 0; // this should be a feature

    public SimpleFilteredStrategy() {
        this(TacletFilter.TRUE);
    }

    public SimpleFilteredStrategy(RuleFilter p_ruleFilter) {
        ruleFilter = p_ruleFilter;
    }

    public Name name() {
        return NAME;
    }

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     *
     * @return the cost of the rule application expressed as a <code>RuleAppCost</code> object.
     *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule shall not be applied at
     *         all (it is discarded by the strategy).
     */
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
        if (app instanceof TacletApp && !ruleFilter.filter(app.rule())) {
            return TopRuleAppCost.INSTANCE;
        }

        RuleAppCost res = NonDuplicateAppFeature.INSTANCE.computeCost(app, pio, goal);
        if (res == TopRuleAppCost.INSTANCE) {
            return res;
        }

        long cost = goal.getTime();
        if (app instanceof TacletApp && !((TacletApp) app).ifInstsComplete()) {
            cost += IF_NOT_MATCHED_MALUS;
        }

        return NumberRuleAppCost.create(cost);
    }

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is called immediately before a rule is really
     * applied
     *
     * @return true iff the rule should be applied, false otherwise
     */
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        // do not apply a rule twice
        return !(app instanceof TacletApp) || NonDuplicateAppFeature.INSTANCE.computeCost(app, pio,
            goal) != TopRuleAppCost.INSTANCE;
    }

    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            RuleAppCostCollector collector) {}

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }
}
