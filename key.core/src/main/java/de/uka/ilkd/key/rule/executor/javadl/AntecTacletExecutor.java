/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.executor.javadl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

/**
 * Executes a Taclet which matches on a formula in the antecedent
 *
 * @author Richard Bubel
 * @param <TacletKind> the kind of taclet this executor is responsible for
 */
public class AntecTacletExecutor<TacletKind extends AntecTaclet>
        extends FindTacletExecutor<TacletKind> {


    public AntecTacletExecutor(TacletKind taclet) {
        super(taclet);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState,
            SequentChangeInfo currentSequent, PosInOccurrence posOfFind, MatchConditions matchCond,
            Goal goal, RuleApp ruleApp, Services services) {
        if (gt instanceof AntecSuccTacletGoalTemplate) {
            final Sequent replWith = ((AntecSuccTacletGoalTemplate) gt).replaceWith();
            replaceAtPos(replWith.antecedent(), termLabelState, currentSequent, posOfFind,
                matchCond, new TacletLabelHint(TacletOperation.REPLACE_AT_ANTECEDENT, replWith),
                goal, ruleApp, services);
            if (!replWith.succedent().isEmpty()) {
                addToSucc(replWith.succedent(), termLabelState,
                    new TacletLabelHint(TacletOperation.REPLACE_TO_SUCCEDENT, replWith),
                    currentSequent, null, posOfFind, matchCond, goal, ruleApp, services);
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
     * @param whereToAdd the {@link PosInOccurrence} where to add the sequent or {@link null} if it
     *        should just be added to the head of the sequent (otherwise it will be tried to add the
     *        new formulas close to that position)
     * @param posOfFind the {@link PosInOccurrence} providing the position information where the
     *        match took place
     * @param matchCond the {@link MatchConditions} with all required instantiations
     * @param goal the Goal where the taclet is applied to
     * @param ruleApp the {@link TacletApp} describing the current ongoing taclet application
     * @param services the {@link Services} encapsulating all Java model information
     */
    @Override
    protected void applyAdd(Sequent add, TermLabelState termLabelState,
            SequentChangeInfo currentSequent, PosInOccurrence whereToAdd, PosInOccurrence posOfFind,
            MatchConditions matchCond, Goal goal, RuleApp ruleApp, Services services) {
        addToAntec(add.antecedent(), termLabelState,
            new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), currentSequent, whereToAdd,
            posOfFind, matchCond, goal, ruleApp, services);
        addToSucc(add.succedent(), termLabelState,
            new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), currentSequent, null,
            posOfFind, matchCond, goal, ruleApp, services);
    }

}
