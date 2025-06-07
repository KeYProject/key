/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.executor.javadl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.util.TermHelper;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;

import org.key_project.logic.IntIterator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.instantiation.MatchConditions;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;

public class RewriteTacletExecutor extends FindTacletExecutor {

    public RewriteTacletExecutor(RewriteTaclet taclet) {
        super(taclet);
    }

    /**
     * does the work for applyReplacewith (wraps recursion)
     */
    private JTerm replace(JTerm term, JTerm with, TermLabelState termLabelState,
            TacletLabelHint labelHint, PosInOccurrence posOfFind,
            IntIterator it,
            MatchConditions mc,
            Sort maxSort, Goal goal, Services services, TacletApp ruleApp) {
        if (it.hasNext()) {
            final int indexOfNextSubTerm = it.next();

            final JTerm[] subs = new JTerm[term.arity()];
            term.subs().arraycopy(0, subs, 0, term.arity());

            final Sort newMaxSort = TermHelper.getMaxSort(term, indexOfNextSubTerm);
            subs[indexOfNextSubTerm] = replace(term.sub(indexOfNextSubTerm), with, termLabelState,
                labelHint, posOfFind, it, mc, newMaxSort, goal, services, ruleApp);

            return services.getTermFactory().createTerm(term.op(), subs, term.boundVars(),
                term.getLabels());
        }

        with = (JTerm) syntacticalReplace(with, posOfFind, mc, goal, ruleApp, services,
            termLabelState, labelHint);

        if (!with.sort().extendsTrans(maxSort)) {
            with = services.getTermBuilder().cast(maxSort, with);
        }

        return with;
    }


    private SequentFormula applyReplacewithHelper(Goal goal,
            TermLabelState termLabelState,
            RewriteTacletGoalTemplate gt, PosInOccurrence posOfFind,
            Services services,
            MatchConditions matchCond,
            TacletApp ruleApp) {
        final JTerm term = (JTerm) posOfFind.sequentFormula().formula();
        final IntIterator it = posOfFind.posInTerm().iterator();
        final JTerm rwTemplate = gt.replaceWith();

        JTerm formula = replace(term, rwTemplate, termLabelState, new TacletLabelHint(rwTemplate),
            posOfFind, it, matchCond, term.sort(), goal, services, ruleApp);
        formula = TermLabelManager.refactorSequentFormula(termLabelState, services, formula,
            posOfFind, taclet, goal, null, rwTemplate);
        if (term == formula) {
            return posOfFind.sequentFormula();
        } else {
            return new SequentFormula(formula);
        }
    }


    public SequentFormula getRewriteResult(Goal goal,
            TermLabelState termLabelState,
            Services services, TacletApp app) {
        assert taclet.goalTemplates().size() == 1;
        assert taclet.goalTemplates().head().sequent().isEmpty();
        assert !taclet
                .applicationRestriction().matches(ApplicationRestriction.IN_SEQUENT_STATE);
        assert app.complete();
        final RewriteTacletGoalTemplate gt =
            (RewriteTacletGoalTemplate) taclet.goalTemplates().head();
        return applyReplacewithHelper(goal, termLabelState, gt, app.posInOccurrence(), services,
            app.matchConditions(), app);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState,
            SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind, MatchConditions matchCond,
            Goal goal, TacletApp ruleApp, Services services) {
        if (gt instanceof RewriteTacletGoalTemplate) {
            final SequentFormula cf =
                applyReplacewithHelper(goal, termLabelState,
                    (RewriteTacletGoalTemplate) gt, posOfFind, services, matchCond, ruleApp);
            currentSequent.combine(currentSequent.sequent().changeFormula(cf, posOfFind));
        } else {
            // Then there was no replacewith...
            // This is strange in a RewriteTaclet, but who knows...
            // However, term label refactorings have to be performed.
            final JTerm oldFormula = (JTerm) posOfFind.sequentFormula().formula();
            final JTerm newFormula = TermLabelManager.refactorSequentFormula(termLabelState,
                services, oldFormula, posOfFind, taclet, goal, null, null);
            if (oldFormula != newFormula) {
                currentSequent.combine(currentSequent.sequent()
                        .changeFormula(new SequentFormula(newFormula), posOfFind));
            }
        }
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     *
     * @param add the Sequent to be added
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param posOfFind describes the application position of the find expression in the original
     *        sequent
     * @param whereToAdd the PosInOccurrence describes the place where to add the semisequent
     * @param matchCond the MatchConditions with all required instantiations
     * @param goal the Goal the taclet is applied to
     * @param ruleApp the rule application to apply
     * @param services the Services encapsulating all java information
     */
    @Override
    protected void applyAdd(Sequent add, TermLabelState termLabelState,
            SequentChangeInfo currentSequent,
            PosInOccurrence whereToAdd, PosInOccurrence posOfFind,
            MatchConditions matchCond, Goal goal, TacletApp ruleApp, Services services) {
        if (posOfFind.isInAntec()) {
            addToAntec(add.antecedent(), currentSequent, whereToAdd, posOfFind, matchCond, goal,
                ruleApp, services, termLabelState,
                new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add));
            addToSucc(add.succedent(), currentSequent, null, posOfFind, matchCond, goal, ruleApp,
                services, termLabelState,
                new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add));
        } else {
            addToAntec(add.antecedent(), currentSequent, null, posOfFind, matchCond, goal, ruleApp,
                services, termLabelState,
                new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add));
            addToSucc(add.succedent(), currentSequent, whereToAdd, posOfFind, matchCond, goal,
                ruleApp, services, termLabelState,
                new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add));
        }
    }
}
