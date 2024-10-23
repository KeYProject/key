/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.executor.rustydl;

import java.util.Iterator;

import org.key_project.logic.PosInTerm;
import org.key_project.ncore.sequent.FormulaChangeInfo;
import org.key_project.ncore.sequent.PosInOccurrence;
import org.key_project.ncore.sequent.SequentChangeInfo;
import org.key_project.ncore.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.rule.*;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;

public abstract class FindTacletExecutor<TacletKind extends FindTaclet>
        extends TacletExecutor<TacletKind> {
    public FindTacletExecutor(TacletKind taclet) {
        super(taclet);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp) {
        final var services = goal.getOverlayServices();
        // Number without the if-goal eventually needed
        final int numberOfNewGoals = taclet.goalTemplates().size();

        final var tacletApp = (TacletApp) ruleApp;
        final MatchConditions mc = tacletApp.matchConditions();

        final ImmutableList<SequentChangeInfo> newSequentsForGoals =
            checkAssumesGoals(goal, tacletApp.assumesFormulaInstantiations(), mc, numberOfNewGoals);

        final ImmutableList<Goal> newGoals = goal.split(newSequentsForGoals.size());

        final Iterator<Goal> goalIt = newGoals.iterator();
        final Iterator<SequentChangeInfo> newSequentsIt = newSequentsForGoals.iterator();

        for (var nextGT : taclet.goalTemplates()) {
            final var gt = (TacletGoalTemplate) nextGT;
            final Goal currentGoal = goalIt.next();
            final SequentChangeInfo currentSequent = newSequentsIt.next();

            applyReplacewith(gt, currentSequent, tacletApp.posInOccurrence(), mc,
                currentGoal, ruleApp, services);

            /*
             * update position information, as original formula may no longer be in the current
             * sequent
             */
            final PosInOccurrence posWhereToAdd =
                updatePositionInformation(tacletApp, gt, currentSequent);

            applyAdd(gt.sequent(), currentSequent, posWhereToAdd,
                tacletApp.posInOccurrence(), mc, goal, ruleApp, services);

            applyAddrule(gt.rules(), currentGoal, services, mc);

            // using position of find here as an eventual program of the subterm needs to be
            // found; this is taken directly from the posinoccurrence and not searched for
            // in the new sequent
            applyAddProgVars(gt.addedProgVars(), currentSequent, currentGoal,
                tacletApp.posInOccurrence(), services, mc);

            currentGoal.setSequent(currentSequent);

            currentGoal.setBranchLabel(gt.name());
        }

        // in case the assumes sequent of the taclet did not
        // already occur in the goal sequent, we had to perform a cut
        // in this loop we make sure to assign the cut goal its correct
        // sequent
        while (newSequentsIt.hasNext()) {
            final Goal nextGoal = goalIt.next();
            nextGoal.setSequent(newSequentsIt.next());
        }

        assert !goalIt.hasNext();

        return newGoals;
    }

    /**
     * applies the {@code add}-expressions of taclet goal descriptions
     *
     * @param add the {@link Sequent} with the uninstantiated {@link SequentFormula}'s to be added
     *        to the goal's sequent
     * @param currentSequent the {@link SequentChangeInfo} which is the current (intermediate)
     *        result of applying the taclet
     * @param whereToAdd the {@link PosInOccurrence} where to add the sequent or {@code null} if it
     *        should just be added to the head of the sequent (otherwise it will be tried to add the
     *        new formulas close to that position)
     * @param posOfFind the {@link PosInOccurrence} providing the position information where the
     *        match took place
     * @param matchCond the {@link MatchConditions} with all required instantiations
     * @param goal the Goal where the taclet is applied to
     * @param ruleApp the {@link TacletApp} describing the current ongoing taclet application
     * @param services the {@link Services} encapsulating all Rust model information
     */
    protected abstract void applyAdd(Sequent add, SequentChangeInfo currentSequent,
            PosInOccurrence whereToAdd, PosInOccurrence posOfFind,
            MatchConditions matchCond, Goal goal, RuleApp ruleApp, Services services);

    /**
     * applies the {@code replacewith}-expression of taclet goal descriptions
     *
     * @param gt the {@link TacletGoalTemplate} used to get the taclet's
     *        {@code replacewith}-expression
     * @param currentSequent the {@link SequentChangeInfo} which is the current (intermediate)
     *        result of applying the taclet
     * @param posOfFind the {@link PosInOccurrence} belonging to the find expression
     * @param matchCond the {@link MatchConditions} with all required instantiations
     * @param goal the {@link Goal} on which the taclet is applied
     * @param ruleApp the {@link TacletApp} describing the current ongoing taclet application
     * @param services the {@link Services} encapsulating all Rust model information
     */
    protected abstract void applyReplacewith(TacletGoalTemplate gt,
            SequentChangeInfo currentSequent, PosInOccurrence posOfFind, MatchConditions matchCond,
            Goal goal, RuleApp ruleApp, Services services);

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
            if (modifiedFormulas != null && !modifiedFormulas.isEmpty()) {
                // add it close to the modified formula
                final FormulaChangeInfo head = modifiedFormulas.head();
                result =
                    new PosInOccurrence(head.newFormula(), PosInTerm.getTopLevel(), inAntec);
            } else {
                // just add it
                result = null;
            }
        }
        return result;
    }
}
