/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;

/**
 * Instances of this class are used to store if a rule could be applied automatically and if not to
 * store the reason why no rule applications could be performed.
 */
public class SingleRuleApplicationInfo {

    private final boolean success;
    private final String message;
    private final ProofGoal<?> goal;
    private final RuleApp appliedRuleApp;

    public SingleRuleApplicationInfo(ProofGoal<?> mayCloseableGoal,
            RuleApp appliedRuleApp) {
        this.message = "Rule applied successful";
        this.goal = mayCloseableGoal;
        this.appliedRuleApp = appliedRuleApp;
        this.success = true;
    }

    public SingleRuleApplicationInfo(String message, ProofGoal<?> nonCloseableGoal,
            RuleApp appliedRuleApp) {
        this.message = message;
        this.goal = nonCloseableGoal;
        this.appliedRuleApp = appliedRuleApp;
        this.success = false;
    }

    public boolean isSuccess() {
        return success;
    }

    public <G extends ProofGoal<G>> G getGoal() {
        return (G) goal;
    }

    public String message() {
        return message;
    }

    public RuleApp getAppliedRuleApp() {
        return appliedRuleApp;
    }
}
