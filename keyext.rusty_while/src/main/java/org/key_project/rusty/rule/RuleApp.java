/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.rusty.Services;
import org.key_project.rusty.proof.Goal;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

public interface RuleApp {
    /**
     * returns the rule of this rule application
     */
    Rule rule();

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     *
     * @param goal the Goal where to apply the rule
     * @param services the Services encapsulating all java information
     * @return list of new created goals
     */
    @Nullable
    ImmutableList<Goal> execute(Goal goal, Services services);

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
}
