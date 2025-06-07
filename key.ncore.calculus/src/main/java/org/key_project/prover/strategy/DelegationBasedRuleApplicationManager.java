/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import org.key_project.prover.proof.ProofGoal;

import org.jspecify.annotations.NonNull;

/// An [RuleApplicationManager] based on delegation.
///
/// @author Dominic Steinhoefel
public interface DelegationBasedRuleApplicationManager<G extends ProofGoal<@NonNull G>>
        extends RuleApplicationManager<G> {
    /// @return The delegate.
    RuleApplicationManager<G> getDelegate();
}
