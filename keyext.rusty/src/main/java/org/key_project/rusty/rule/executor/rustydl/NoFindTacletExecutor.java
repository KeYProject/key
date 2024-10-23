/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.executor.rustydl;

import java.util.Iterator;

import org.key_project.ncore.sequent.SequentChangeInfo;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.rule.*;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;

public class NoFindTacletExecutor extends TacletExecutor<NoFindTaclet> {
    public NoFindTacletExecutor(NoFindTaclet taclet) {
        super(taclet);
    }

    /**
     * the rule is applied on the given goal using the information of rule application.
     *
     * @param goal the goal that the rule application should refer to.
     * @param ruleApp the taclet application that is executed
     */
    @Override
    public ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp) {
        // Number without the if-goal eventually needed
        int numberOfNewGoals = taclet.goalTemplates().size();

        var tacletApp = (TacletApp) ruleApp;
        MatchConditions mc = tacletApp.matchConditions();

        ImmutableList<SequentChangeInfo> newSequentsForGoals =
            checkAssumesGoals(goal, tacletApp.assumesFormulaInstantiations(), mc, numberOfNewGoals);

        ImmutableList<Goal> newGoals = goal.split(newSequentsForGoals.size());

        var it = taclet.goalTemplates().iterator();
        Iterator<Goal> goalIt = newGoals.iterator();
        Iterator<SequentChangeInfo> newSequentsIt = newSequentsForGoals.iterator();

        final var services = goal.getOverlayServices();
        while (it.hasNext()) {
            TacletGoalTemplate gt = (TacletGoalTemplate) it.next();
            Goal currentGoal = goalIt.next();
            // add first because we want to use pos information that
            // is lost applying replacewith

            SequentChangeInfo currentSequent = newSequentsIt.next();

            applyAdd(gt.sequent(), currentSequent, services, mc, goal, ruleApp);

            applyAddrule(gt.rules(), currentGoal, services, mc);

            applyAddProgVars(gt.addedProgVars(), currentSequent, currentGoal,
                tacletApp.posInOccurrence(), services, mc);

            currentGoal.setSequent(currentSequent);

            currentGoal.setBranchLabel(gt.name());
        }

        return newGoals;
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     *
     * @param add the Sequent to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param services the Services encapsulating all Rust information
     * @param matchCond the MatchConditions with all required instantiations
     */
    protected void applyAdd(Sequent add,
            SequentChangeInfo currentSequent, Services services, MatchConditions matchCond,
            Goal goal, RuleApp ruleApp) {
        addToAntec(add.antecedent(),
            currentSequent, null, null,
            matchCond, goal, ruleApp, services);
        addToSucc(add.succedent(),
            currentSequent, null, null,
            matchCond, goal, ruleApp, services);
    }
}
