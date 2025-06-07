/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.executor.javadl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.instantiation.MatchConditions;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;

/**
 * Executes a Taclet which matches on a formula in the antecedent
 *
 * @author Richard Bubel
 */
public class AntecTacletExecutor extends FindTacletExecutor {

    public AntecTacletExecutor(AntecTaclet taclet) {
        super(taclet);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState,
            SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind, MatchConditions matchCond,
            Goal goal, TacletApp ruleApp, Services services) {
        if (gt instanceof AntecSuccTacletGoalTemplate template) {
            final Sequent replWith = template.replaceWith();
            replaceAtPos(replWith.antecedent(), currentSequent, posOfFind, matchCond, goal, ruleApp,
                services, termLabelState,
                new TacletLabelHint(TacletOperation.REPLACE_AT_ANTECEDENT, replWith));
            if (!replWith.succedent().isEmpty()) {
                addToSucc(replWith.succedent(), currentSequent, null, posOfFind, matchCond, goal,
                    ruleApp, services, termLabelState,
                    new TacletLabelHint(TacletOperation.REPLACE_TO_SUCCEDENT, replWith));
            }
        } else {
            // Then there was no replacewith...
        }
    }


    /**
     * applies the {@code add}-expressions of taclet goal descriptions
     *
     * @param add the {@link Sequent} with the uninstantiated {@link SequentFormula}'s to be added
     *        to the goal's sequent
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param currentSequent the {@link SequentChangeInfo} which is the current (intermediate)
     *        result of applying the taclet
     * @param whereToAdd the {@link PosInOccurrence} where to add the sequent or {@code null} if it
     *        should just be added to the head of the sequent (otherwise it will be tried to add the
     *        new formulas close to that position)
     * @param posOfFind the {@link PosInOccurrence} providing the position information where the
     *        match took place
     * @param matchCond the {@link MatchConditions} with all required instantiations
     * @param goal the Goal where the taclet is applied to
     * @param ruleApp the {@link RuleApp} (a TacletApp) describing the current ongoing taclet
     *        application
     * @param services the {@link Services} encapsulating all Java model information
     */
    @Override
    protected void applyAdd(Sequent add, TermLabelState termLabelState,
            SequentChangeInfo currentSequent,
            PosInOccurrence whereToAdd,
            PosInOccurrence posOfFind,
            MatchConditions matchCond, Goal goal, TacletApp ruleApp, Services services) {
        addToAntec(add.antecedent(), currentSequent, whereToAdd, posOfFind, matchCond, goal,
            ruleApp, services, termLabelState,
            new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add));
        addToSucc(add.succedent(), currentSequent, null, posOfFind, matchCond, goal, ruleApp,
            services, termLabelState,
            new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add));
    }

}
