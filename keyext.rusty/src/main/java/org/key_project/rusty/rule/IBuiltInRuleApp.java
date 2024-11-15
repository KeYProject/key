/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.proof.Goal;
import org.key_project.util.collection.ImmutableList;

public interface IBuiltInRuleApp extends RuleApp {
    /**
     * returns the built-in rule of this rule application
     */
    BuiltInRule rule();

    /**
     * Tries to complete the rule application from the available information.
     */
    IBuiltInRuleApp tryToInstantiate(Goal goal);

    IBuiltInRuleApp forceInstantiate(Goal goal);

    /**
     * @return true if tryToInstantiate may be able to complete the app
     */
    boolean isSufficientlyComplete();

    ImmutableList<PosInOccurrence> ifInsts();

    IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts);

    IBuiltInRuleApp replacePos(PosInOccurrence newPos);
}
