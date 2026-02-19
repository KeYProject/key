/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.LogicServices;
import org.key_project.prover.rules.RuleExecutor;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Built-in rule interface. As applications of this rule kind may not be successful, in each case
 * one
 * has to ensure that the goal split is done only iff the application was successful.
 */
@NullMarked
public interface BuiltInRule extends org.key_project.prover.rules.IBuiltInRule<Goal>, Rule {

    IBuiltInRuleApp createApp(@Nullable PosInOccurrence pos, LogicServices services);

    @Override
    default RuleExecutor<Goal> getExecutor() {
        return this;
    }

    @Override
    default @Nullable String getOrigin() {
        return "defined in Java: " + getClass().getName();
    }
}
