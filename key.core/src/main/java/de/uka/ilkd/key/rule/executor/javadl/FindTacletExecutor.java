/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.executor.javadl;

import java.util.Iterator;
import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

import org.key_project.util.collection.ImmutableList;

public abstract class FindTacletExecutor<TacletKind extends FindTaclet>
        extends TacletExecutor<TacletKind> {
    public static final AtomicLong PERF_APPLY = new AtomicLong();
    public static final AtomicLong PERF_SET_SEQUENT = new AtomicLong();
    public static final AtomicLong PERF_TERM_LABELS = new AtomicLong();

    public FindTacletExecutor(TacletKind taclet) {
        super(taclet);
    }


    /**
     * applies the {@code replacewith}-expression of taclet goal descriptions
     *
     * @param gt the {@link TacletGoalTemplate} used to get the taclet's
     *        {@code replacewith}-expression
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param currentSequent the {@link SequentChangeInfo} which is the current (intermediate)
     *        result of applying the taclet
     * @param posOfFind the {@link PosInOccurrence} belonging to the find expression
     * @param matchCond the {@link MatchConditions} with all required instantiations
     * @param goal the {@link Goal} on which the taclet is applied
     * @param ruleApp the {@link TacletApp} describing the current ongoing taclet application
     * @param services the {@link Services} encapsulating all Java model information
     */
    protected abstract void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState,
            SequentChangeInfo currentSequent, PosInOccurrence posOfFind, MatchConditions matchCond,
            Goal goal, RuleApp ruleApp, Services services);


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
    protected abstract void applyAdd(Sequent add, TermLabelState termLabelState,
            SequentChangeInfo currentSequent, PosInOccurrence whereToAdd, PosInOccurrence posOfFind,
            MatchConditions matchCond, Goal goal, RuleApp ruleApp, Services services);



    /**
     * the rule is applied on the given goal using the information of rule application.
     *
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the taclet application that is executed.
     */
    @Override
    public final ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
        final TermLabelState termLabelState = new TermLabelState();
        // Number without the if-goal eventually needed
        final int numberOfNewGoals = taclet.goalTemplates().size();

        final TacletApp tacletApp = (TacletApp) ruleApp;
        final MatchConditions mc = tacletApp.matchConditions();

        final ImmutableList<SequentChangeInfo> newSequentsForGoals =
            checkIfGoals(goal, tacletApp.ifFormulaInstantiations(), mc, numberOfNewGoals);

        final ImmutableList<Goal> newGoals = goal.split(newSequentsForGoals.size());

        final Iterator<TacletGoalTemplate> it = taclet.goalTemplates().iterator();
        final Iterator<Goal> goalIt = newGoals.iterator();
        final Iterator<SequentChangeInfo> newSequentsIt = newSequentsForGoals.iterator();

        while (it.hasNext()) {
            final TacletGoalTemplate gt = it.next();
            final Goal currentGoal = goalIt.next();
            final SequentChangeInfo currentSequent = newSequentsIt.next();

            var timeApply = System.nanoTime();
            applyReplacewith(gt, termLabelState, currentSequent, tacletApp.posInOccurrence(), mc,
                currentGoal, ruleApp, services);

            /*
             * update position information, as original formula may no longer be in the current
             * sequent
             */
            final PosInOccurrence posWhereToAdd =
                updatePositionInformation(tacletApp, gt, currentSequent);

            applyAdd(gt.sequent(), termLabelState, currentSequent, posWhereToAdd,
                tacletApp.posInOccurrence(), mc, goal, ruleApp, services);

            applyAddrule(gt.rules(), currentGoal, services, mc);

            // using position of find here as an eventual program of the subterm needs to be
            // found; this is taken directly from the posinoccurrence and not searched for
            // in the new sequent
            applyAddProgVars(gt.addedProgVars(), currentSequent, currentGoal,
                tacletApp.posInOccurrence(), services, mc);
            PERF_APPLY.getAndAdd(System.nanoTime() - timeApply);

            var timeTermLabels = System.nanoTime();
            TermLabelManager.mergeLabels(currentSequent, services);
            timeTermLabels = System.nanoTime() - timeTermLabels;

            var timeSetSequent = System.nanoTime();
            currentGoal.setSequent(currentSequent);
            PERF_SET_SEQUENT.getAndAdd(System.nanoTime() - timeSetSequent);

            var nfn = gt.getBranchNamingFunction();
            if (nfn == null)
                currentGoal.setBranchLabel(gt.name());
            else
                currentGoal.setBranchLabel(
                    nfn.getName(services, currentSequent, tacletApp, mc));

            timeTermLabels = System.nanoTime() + timeTermLabels;
            TermLabelManager.refactorSequent(termLabelState, services, ruleApp.posInOccurrence(),
                ruleApp.rule(), currentGoal, null, null);
            PERF_TERM_LABELS.getAndAdd(System.nanoTime() - timeTermLabels);
        }

        // in case the assumes sequent of the taclet did not
        // already occur in the goal sequent, we had to perform a cut
        // in this loop we make sure to assign the cut goal its correct
        // sequent
        while (newSequentsIt.hasNext()) {
            final Goal nextGoal = goalIt.next();
            nextGoal.setSequent(newSequentsIt.next());
            TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(),
                ruleApp.rule(), nextGoal, null, null);
        }

        assert !goalIt.hasNext();

        return newGoals;
    }


    /**
     * creates a new position information object, describing where to add the formulas or
     * {@code null} if it should just be added to the beginning
     *
     * @param tacletApp a TacletApp with application information
     * @param gt the TacletGoalTemplate to be applied
     * @param currentSequent the current sequent (the one of the new goal)
     * @return the PosInOccurrence object describing where to add the formula
     */
    private PosInOccurrence updatePositionInformation(TacletApp tacletApp, TacletGoalTemplate gt,
            SequentChangeInfo currentSequent) {
        PosInOccurrence result = tacletApp.posInOccurrence();

        if (result != null && gt.replaceWithExpressionAsObject() != null) {
            final boolean inAntec = result.isInAntec();
            final ImmutableList<FormulaChangeInfo> modifiedFormulas =
                currentSequent.modifiedFormulas(inAntec);
            if (modifiedFormulas != null && modifiedFormulas.size() > 0) {
                // add it close to the modified formula
                final FormulaChangeInfo head = modifiedFormulas.head();
                result =
                    new PosInOccurrence(head.getNewFormula(), PosInTerm.getTopLevel(), inAntec);
            } else {
                // just add it
                result = null;
            }
        }
        return result;
    }
}
