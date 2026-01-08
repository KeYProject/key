/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.Arrays;
import java.util.HashSet;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.RuleApplicationManager;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class DelegatingRuleAppManager implements RuleApplicationManager<Goal> {

    private static String[] ruleSetNames =
        { "alpha", "concrete", "simplify", "simplify_prog", "simplify_expression" };

    private HashSet<String> ruleSets = new HashSet<>();

    private final RuleApplicationManager<Goal> costBasedAppManager;
    private ImmutableList<RuleAppContainer> queue;
    private Goal goal;
    private RuleApp nextApp;

    public DelegatingRuleAppManager(RuleApplicationManager<Goal> costRuleAppMgr) {
        this.costBasedAppManager = costRuleAppMgr;
        queue = ImmutableSLList.nil();
        ruleSets.addAll(Arrays.asList(ruleSetNames));
    }

    @Override
    public void clearCache() {
        costBasedAppManager.clearCache();
    }

    @Override
    public RuleApp peekNext() {
        RuleApp next = nextApp;
        if (next == null && !queue.isEmpty()) {
            var myQueue = queue;
            while (next == null && !myQueue.isEmpty()) {
                next = myQueue.head().completeRuleApp(goal);
                myQueue = myQueue.tail();
            }
            queue = myQueue;
        }
        nextApp = next == null ? costBasedAppManager.peekNext() : next;
        return nextApp;
    }

    @Override
    public RuleApp next() {
        final RuleApp next = peekNext();
        nextApp = null;
        return next;
    }

    @Override
    public RuleApplicationManager<Goal> copy() {
        DelegatingRuleAppManager copy = new DelegatingRuleAppManager(costBasedAppManager.copy());
        copy.queue = queue;
        return copy;
    }

    @Override
    public void setGoal(Goal p_goal) {
        this.goal = p_goal;
        costBasedAppManager.setGoal(p_goal);
    }

    @Override
    public void ruleAdded(RuleApp rule, PosInOccurrence pos) {
        if (rule instanceof NoPosTacletApp tapp && tapp.taclet().getRuleSets().size() == 1 &&
                tapp.taclet().getRuleSets().exists(rs -> ruleSets.contains(rs.name().toString()))) {
            queue = queue.prepend(new FindTacletAppContainer(tapp, pos,
                NumberRuleAppCost.getZeroCost(), goal, goal.getTime()));
        } else {
            costBasedAppManager.ruleAdded(rule, pos);
        }
    }

    @Override
    public void rulesAdded(ImmutableList<? extends RuleApp> rule, PosInOccurrence pos) {
        for (RuleApp ruleApp : rule) {
            ruleAdded(ruleApp, pos);
        }
    }
}
