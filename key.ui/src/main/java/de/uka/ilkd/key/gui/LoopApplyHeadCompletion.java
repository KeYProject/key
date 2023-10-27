/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopApplyHeadBuiltInRuleApp;

/**
 * Interactive completion for {@link LoopApplyHeadBuiltInRuleApp}.
 */
public class LoopApplyHeadCompletion implements InteractiveRuleApplicationCompletion {

    LoopApplyHeadCompletion(MainWindow mainWindow) {}

    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp application, final Goal goal,
            final boolean force) {
        LoopApplyHeadBuiltInRuleApp result = (LoopApplyHeadBuiltInRuleApp) application;
        if (!result.complete() && result.cannotComplete(goal)) {
            return result;
        }

        result.tryToInstantiate(goal);
        return result;
    }

    @Override
    public boolean canComplete(final IBuiltInRuleApp app) {
        return app instanceof LoopApplyHeadBuiltInRuleApp;
    }
}
