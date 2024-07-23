/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.rusty.Services;
import org.key_project.rusty.proof.Goal;
import org.key_project.util.collection.ImmutableList;

public abstract class TacletExecutor<T extends Taclet> {
    private static final String AUTO_NAME = "_taclet";

    protected final T taclet;

    public TacletExecutor(T taclet) {
        this.taclet = taclet;
    }

    /**
     * applies the given rule application to the specified goal
     *
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the rule application that is executed.
     * @return List of the goals created by the rule which have to be proved. If this is a
     *         close-goal-taclet ( this.closeGoal () ), the first goal of the return list is the
     *         goal that should be closed (with the constraint this taclet is applied under).
     */
    public abstract ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp);
}
