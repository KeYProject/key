/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.executor.rustydl;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentChangeInfo;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.RewriteTaclet;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;

public class RewriteTacletExecutor<TacletKind extends RewriteTaclet>
        extends FindTacletExecutor<TacletKind> {

    public RewriteTacletExecutor(TacletKind taclet) {
        super(taclet);
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     *
     * @param add the Sequent to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param posOfFind describes the application position of the find expression in the original
     *        sequent
     * @param whereToAdd the PosInOccurrence describes the place where to add the semisequent
     * @param matchCond the MatchConditions with all required instantiations
     * @param goal the Goal the taclet is applied to
     * @param ruleApp the rule application to apply
     * @param services the Services encapsulating all Rust information
     */
    @Override
    protected void applyAdd(Sequent add,
            SequentChangeInfo currentSequent, PosInOccurrence whereToAdd, PosInOccurrence posOfFind,
            MatchConditions matchCond, Goal goal, RuleApp ruleApp, Services services) {
        if (posOfFind.isInAntec()) {
            addToAntec(add.antecedent(),
                currentSequent,
                whereToAdd, posOfFind, matchCond, goal, ruleApp, services);
            addToSucc(add.succedent(),
                currentSequent, null,
                posOfFind, matchCond, goal, ruleApp, services);
        } else {
            addToAntec(add.antecedent(),
                currentSequent, null,
                posOfFind, matchCond, goal, ruleApp, services);
            addToSucc(add.succedent(),
                currentSequent, whereToAdd,
                posOfFind, matchCond, goal, ruleApp, services);
        }
    }

    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind, MatchConditions matchCond, Goal goal, RuleApp ruleApp,
            Services services) {

    }
}
