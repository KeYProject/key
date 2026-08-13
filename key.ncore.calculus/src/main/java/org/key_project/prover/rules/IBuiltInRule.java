/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.LogicServices;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NonNull;

public interface IBuiltInRule<GOAL extends ProofGoal<GOAL>> extends Rule, RuleExecutor<GOAL> {
    /**
     * returns true iff a rule is applicable at the given position. This does not necessarily mean
     * that a rule application will change the goal (this decision is made due to performance
     * reasons)
     */
    boolean isApplicable(GOAL goal, PosInOccurrence pio);

    boolean isApplicableOnSubTerms();

    IBuiltInRuleApp createApp(PosInOccurrence pos, LogicServices services);

    @Override
    default @NonNull RuleExecutor<@NonNull GOAL> getExecutor() {
        return this;
    }

}
