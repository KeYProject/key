/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.util.collection.ImmutableList;

/** A contentless container for tests that drive the parked map without a rule application. */
final class StubRuleAppContainer extends RuleAppContainer {

    StubRuleAppContainer() {
        super(null, NumberRuleAppCost.getZeroCost());
    }

    @Override
    public ImmutableList<RuleAppContainer> createFurtherApps(Goal goal) {
        return ImmutableList.nil();
    }

    @Override
    public RuleApp completeRuleApp(Goal goal) {
        throw new UnsupportedOperationException("stub");
    }
}
