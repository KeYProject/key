/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NonNull;


public interface RuleApp {
    /**
     * returns the rule of this rule application
     */
    Rule rule();

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     *
     * @TODO: better name
     */
    void execute(Namespace<@NonNull Function> fns);

    /**
     * returns true if all variables are instantiated
     *
     * @return true if all variables are instantiated
     */
    boolean complete();

    /**
     * @return user-friendly name for this rule-application
     */
    default String displayName() {
        return rule().displayName();
    }

    PosInOccurrence posInOccurrence();
}
