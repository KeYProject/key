/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.feature.MutableState;

public abstract class FilterStrategy implements Strategy {

    private final Strategy delegate;

    public FilterStrategy(Strategy delegate) {
        this.delegate = delegate;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return delegate.isApprovedApp(app, pio, goal);
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        if (!isApprovedApp(app, pio, goal)) {
            return TopRuleAppCost.INSTANCE;
        }
        return delegate.computeCost(app, pio, goal, mState);
    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            RuleAppCostCollector collector) {
        delegate.instantiateApp(app, pio, goal, collector);
    }

}
