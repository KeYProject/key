/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.executor.javadl;

import java.util.Iterator;
import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.util.PerfScope;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.util.collection.ImmutableList;

public class NoFindTacletExecutor extends TacletExecutor {
    public static final AtomicLong PERF_APPLY = new AtomicLong();
    public static final AtomicLong PERF_SET_SEQUENT = new AtomicLong();
    public static final AtomicLong PERF_TERM_LABELS = new AtomicLong();

    public NoFindTacletExecutor(NoFindTaclet taclet) {
        super(taclet);
    }

    @Override
    public ImmutableList<SequentChangeInfo> getResultSequentChanges(Goal goal, RuleApp ruleApp) {
        final TermLabelState termLabelState = new TermLabelState();
        final Services services = goal.getOverlayServices();
        final TacletApp tacletApp = (TacletApp) ruleApp;
        final MatchConditions mc = tacletApp.matchConditions();

        final ImmutableList<SequentChangeInfo> newSequentsForGoals = checkAssumesGoals(goal,
            tacletApp.assumesFormulaInstantiations(), mc, taclet.goalTemplates().size());

        ImmutableList<SequentChangeInfo> result = ImmutableList.nil();
        final Iterator<SequentChangeInfo> it = newSequentsForGoals.iterator();
        for (var gt : taclet.goalTemplates()) {
            final SequentChangeInfo currentSequent = it.next();
            applyAdd(termLabelState, gt.sequent(), currentSequent, mc, goal, tacletApp);
            TermLabelManager.mergeLabels(currentSequent, services);
            result = result.append(currentSequent);
        }
        while (it.hasNext()) {
            result = result.append(it.next());
        }
        return result;
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     *
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param add the Sequent to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param matchCond the MatchConditions with all required instantiations
     */
    protected void applyAdd(TermLabelState termLabelState, Sequent add,
            SequentChangeInfo currentSequent,
            MatchConditions matchCond,
            Goal goal, TacletApp ruleApp) {
        addToAntec(add.antecedent(), currentSequent, null, null, matchCond, goal, ruleApp,
            goal.getOverlayServices(), termLabelState,
            new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add));
        addToSucc(add.succedent(), currentSequent, null, null, matchCond, goal, ruleApp,
            goal.getOverlayServices(), termLabelState,
            new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add));
    }

    /**
     * the rule is applied on the given goal using the information of rule application.
     *
     * @param goal the goal that the rule application should refer to.
     * @param ruleApp the taclet application that is executed
     */
    public ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp) {
        final TermLabelState termLabelState = new TermLabelState();

        // Number without the if-goal eventually needed
        int numberOfNewGoals = taclet.goalTemplates().size();

        final TacletApp tacletApp = (TacletApp) ruleApp;
        MatchConditions mc = tacletApp.matchConditions();

        ImmutableList<SequentChangeInfo> newSequentsForGoals =
            checkAssumesGoals(goal, tacletApp.assumesFormulaInstantiations(), mc, numberOfNewGoals);

        ImmutableList<Goal> newGoals = goal.split(newSequentsForGoals.size());

        Iterator<Goal> goalIt = newGoals.iterator();
        Iterator<SequentChangeInfo> newSequentsIt =
            newSequentsForGoals.iterator();

        final var services = goal.getOverlayServices();
        for (var gt : taclet.goalTemplates()) {
            Goal currentGoal = goalIt.next();
            // add first because we want to use pos information that
            // is lost applying replacewith

            SequentChangeInfo currentSequent = newSequentsIt.next();

            final long timeApply = PerfScope.start();
            applyAdd(termLabelState, gt.sequent(), currentSequent, mc, goal, tacletApp);

            applyAddrule(gt.rules(), currentGoal, services, mc);

            applyAddProgVars(gt.addedProgVars(), currentSequent, currentGoal,
                tacletApp.posInOccurrence(), services, mc);
            PerfScope.stop(PERF_APPLY, timeApply);

            final long timeMergeLabels = PerfScope.start();
            TermLabelManager.mergeLabels(currentSequent, services);
            PerfScope.stop(PERF_TERM_LABELS, timeMergeLabels);

            final long timeSetSequent = PerfScope.start();
            currentGoal.setSequent(currentSequent);
            PerfScope.stop(PERF_SET_SEQUENT, timeSetSequent);

            currentGoal.setBranchLabel(gt.name());
            final long timeRefactorLabels = PerfScope.start();
            TermLabelManager.refactorSequent(termLabelState, services,
                ruleApp.posInOccurrence(),
                ruleApp.rule(), currentGoal, null, null);
            PerfScope.stop(PERF_TERM_LABELS, timeRefactorLabels);
        }

        return newGoals;
    }
}
