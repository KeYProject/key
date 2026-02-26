/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import java.util.Set;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.IBuiltInRule;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.strategy.costbased.feature.RuleSetDispatchFeature;

public interface ComponentStrategy<GOAL extends ProofGoal<GOAL>> extends Strategy<GOAL> {
    enum StrategyAspect {
        Cost, Instantiation, Approval;
    }

    /// The strategy's cost dispatcher.
    RuleSetDispatchFeature getDispatcher(StrategyAspect aspect);

    /// The rule sets this strategy is designed to handle.
    Set<RuleSet> getResponsibilities(StrategyAspect aspect);

    /// Whether this strategy is responsible for the given [IBuiltInRule]. This is necessary as
    /// built-in rules have no rule sets.
    boolean isResponsibleFor(IBuiltInRule rule);
}
