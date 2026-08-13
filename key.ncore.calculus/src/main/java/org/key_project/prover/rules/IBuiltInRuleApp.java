/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

public interface IBuiltInRuleApp<Goal extends ProofGoal<Goal>> extends RuleApp {

    /**
     * Tries to complete the rule application from the available information.
     */
    IBuiltInRuleApp<Goal> tryToInstantiate(Goal goal);

    IBuiltInRuleApp<Goal> forceInstantiate(Goal goal);

    /**
     * returns true if tryToInstantiate is able to complete the app
     *
     * @return true if tryToInstantiate is able to complete the app
     */
    boolean isSufficientlyComplete();

    ImmutableList<PosInOccurrence> assumesInsts();

    IBuiltInRuleApp<Goal> setAssumesInsts(ImmutableList<PosInOccurrence> ifInsts);

    IBuiltInRuleApp<Goal> replacePos(PosInOccurrence newPos);

    /**
     * returns the built-in rule of this rule application
     */
    IBuiltInRule<Goal> rule();
}
