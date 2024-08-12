/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.executor.rustydl;

import org.key_project.rusty.Services;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.rule.NoFindTaclet;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.rule.TacletExecutor;
import org.key_project.util.collection.ImmutableList;

public class NoFindTacletExecutor extends TacletExecutor<NoFindTaclet> {
    public NoFindTacletExecutor(NoFindTaclet taclet) {
        super(taclet);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
        return null;
    }


}
