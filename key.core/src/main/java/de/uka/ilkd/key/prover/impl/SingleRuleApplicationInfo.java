/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Instances of this class are used to store if a rule could be applied automatically and if not to
 * store the reason why no rule applications could be performed. Because of performance reason the
 * success case returns the singleton {@link SingleRuleApplicationInfo#SUCCESS}
 */
public class SingleRuleApplicationInfo {

    private final boolean success;
    private final String message;
    private final Goal goal;
    private final RuleApp appliedRuleApp;

    SingleRuleApplicationInfo(Goal mayCloseableGoal, RuleApp appliedRuleApp) {
        this.message = "Rule applied successful";
        this.goal = mayCloseableGoal;
        this.appliedRuleApp = appliedRuleApp;
        this.success = true;
    }

    SingleRuleApplicationInfo(String message, Goal nonCloseableGoal, RuleApp appliedRuleApp) {
        this.message = message;
        this.goal = nonCloseableGoal;
        this.appliedRuleApp = appliedRuleApp;
        this.success = false;
    }

    public boolean isSuccess() {
        return success;
    }

    public Goal getGoal() {
        return goal;
    }

    public String message() {
        return message;
    }

    public RuleApp getAppliedRuleApp() {
        return appliedRuleApp;
    }
}
