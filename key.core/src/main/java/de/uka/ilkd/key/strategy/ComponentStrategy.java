/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.Set;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;

import org.key_project.prover.rules.RuleSet;

public interface ComponentStrategy extends Strategy<Goal> {
    enum StrategyAspect {
        Cost, Instantiation, Approval;
    }

    /// The strategy's cost dispatcher.
    RuleSetDispatchFeature getDispatcher(StrategyAspect aspect);

    /// The rule sets this strategy is designed to handle.
    Set<RuleSet> getResponsibilities(StrategyAspect aspect);

    /// Whether this strategy is responsible for the given [BuiltInRule]. This is necessary as
    /// built-in rules have no rule sets.
    boolean isResponsibleFor(BuiltInRule rule);
}
