/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.prover.proof.ProofGoal;

import org.jspecify.annotations.NonNull;

public interface Rule extends Named {
    /**
     * the name of the rule
     */
    @NonNull
    Name name();

    /**
     * returns the display name of the rule
     */
    default String displayName() {
        return name().toString();
    }

    <G extends ProofGoal<G>> RuleExecutor<G> getExecutor();
}
