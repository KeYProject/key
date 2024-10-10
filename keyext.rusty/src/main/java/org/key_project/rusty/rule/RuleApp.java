/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.proof.Goal;

import org.jspecify.annotations.NonNull;


public interface RuleApp extends org.key_project.ncore.rules.RuleApp<@NonNull Goal> {
    /**
     * returns the rule of this rule application
     */
    @Override
    Rule rule();

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula) of this rule application
     */
    PosInOccurrence posInOccurrence();

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     *
     * @param services
     * @return list of new created goals
     */
    @Override
    void execute(Namespace<? super @NonNull Function> fns);

    /**
     * returns true if all variables are instantiated
     *
     * @return true if all variables are instantiated
     */
    @Override
    boolean complete();

    /**
     * @return user-friendly name for this rule-application
     */
    default String displayName() {
        return rule().displayName();
    }
}
