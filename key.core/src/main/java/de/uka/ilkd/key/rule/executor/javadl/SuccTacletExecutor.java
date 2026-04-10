/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.executor.javadl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;

import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;

public class SuccTacletExecutor extends FindTacletExecutor {

    public SuccTacletExecutor(SuccTaclet taclet) {
        super(taclet);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState,
            SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind,
            MatchResultInfo matchCond,
            Goal goal, TacletApp ruleApp, Services services) {
        if (gt instanceof AntecSuccTacletGoalTemplate) {
            final Sequent replWith = ((AntecSuccTacletGoalTemplate) gt).replaceWith();

            replaceAtPos(replWith.succedent(), currentSequent, posOfFind, matchCond, goal, ruleApp,
                services, termLabelState,
                new TacletLabelHint(TacletOperation.REPLACE_AT_SUCCEDENT, replWith));
            if (!replWith.antecedent().isEmpty()) {
                addToAntec(replWith.antecedent(), currentSequent, null, posOfFind, matchCond, goal,
                    ruleApp, services, termLabelState,
                    new TacletLabelHint(TacletOperation.REPLACE_TO_ANTECEDENT, replWith));
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void applyAdd(Sequent add, TermLabelState termLabelState,
            SequentChangeInfo currentSequent,
            PosInOccurrence whereToAdd, PosInOccurrence posOfFind,
            MatchResultInfo matchCond, Goal goal, TacletApp ruleApp, Services services) {
        addToAntec(add.antecedent(), currentSequent, null, posOfFind, matchCond, goal, ruleApp,
            services, termLabelState,
            new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add));
        addToSucc(add.succedent(), currentSequent, whereToAdd, posOfFind, matchCond, goal, ruleApp,
            services, termLabelState,
            new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add));
    }
}
