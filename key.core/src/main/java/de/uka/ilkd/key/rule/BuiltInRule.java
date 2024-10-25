/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.ncore.proof.ProofGoal;
import org.key_project.ncore.rules.RuleApp;
import org.key_project.ncore.rules.RuleExecutor;
import org.key_project.ncore.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Buit-in rule interface. As applications of this rule kind may not be successful in each case one
 * has to ensure that the goal split is done only iff the application was successful.
 */
public interface BuiltInRule extends Rule, RuleExecutor {

    /**
     * returns true iff a rule is applicable at the given position. This does not necessarily mean
     * that a rule application will change the goal (this decision is made due to performance
     * reasons)
     */
    boolean isApplicable(Goal goal, PosInOccurrence pio);

    boolean isApplicableOnSubTerms();

    IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services);

    @Override
    default <Goal extends @NonNull ProofGoal<Goal>> ImmutableList<Goal> apply(ProofGoal<Goal> goal,
            RuleApp ruleApp) {
        return (ImmutableList<Goal>) apply((de.uka.ilkd.key.proof.Goal) goal,
            (de.uka.ilkd.key.rule.RuleApp) ruleApp);
    }

    ImmutableList<Goal> apply(Goal goal, de.uka.ilkd.key.rule.RuleApp ruleApp);

    @Override
    default RuleExecutor getExecutor() {
        return this;
    }

    @Override
    default @Nullable String getOrigin() {
        return "defined in Java: " + getClass().getName();
    }
}
