/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.Named;
import org.key_project.prover.proof.ProofGoal;

import org.jspecify.annotations.NonNull;

/// The interface to be implemented by all types of rules of the system.
/// It provides access to the rule application logic.
public interface Rule extends Named {

    /// Returns the rule executor for this rule.
    /// The rule executor encapsulates the logic for rule applications.
    ///
    /// @return the rule executor for this rule
    /// @param <G> kind of goal on which the executor operates
    @NonNull
    <G extends ProofGoal<G>> RuleExecutor<G> getExecutor();

    /// returns the display name of the rule
    /// by default the name is the same as the rules unique name
    default @NonNull String displayName() {
        return name().toString();
    }

}
