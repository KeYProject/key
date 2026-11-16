/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.gui;

import java.util.Collection;
import java.util.HashSet;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.useractions.UserAction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.automation.IsabelleResult;
import org.key_project.isabelletranslation.automation.IsabelleRule;
import org.key_project.isabelletranslation.automation.IsabelleSolver;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class IsabelleProofApplyUserAction extends UserAction {
    private final Collection<IsabelleSolver> solvers;

    private final Collection<Goal> goalsClosed = new HashSet<>();

    private final int numberOfGoalsClosed;

    private final Collection<Node> originalProofNodes;

    private final @Nullable Node originalSelectedNode;

    public IsabelleProofApplyUserAction(KeYMediator mediator, Proof proof,
            Collection<IsabelleSolver> solvers) {
        super(mediator, proof);
        originalProofNodes = proof.openGoals().stream().map(Goal::node).toList();
        originalSelectedNode = mediator.getSelectedNode();
        this.solvers = solvers;
        this.numberOfGoalsClosed = (int) solvers.stream().filter(solver -> {
            IsabelleResult result = solver.getFinalResult();
            if (result == null) {
                throw new NullPointerException("Solver has no final result.");
            }
            return result.isSuccessful();
        }).count();
    }

    @Override
    public String name() {
        return String.format("Close: %d goals by Isabelle", numberOfGoalsClosed);
    }

    @Override
    protected void apply() {
        for (IsabelleSolver solver : solvers) {
            IsabelleProblem problem = solver.getProblem();
            Goal goal = problem.getGoal();

            IsabelleResult result = solver.getFinalResult();
            if (result == null) {
                throw new NullPointerException("Solver has no final result.");
            }
            if (goalsClosed.contains(goal) || !result.isSuccessful()) {
                continue;
            }

            goalsClosed.add(goal);

            String successfulTactic = result.getSuccessfulTactic();
            if (successfulTactic == null) {
                throw new NullPointerException("Successful solver result has no tactic.");
            }
            IBuiltInRuleApp app =
                IsabelleRule.INSTANCE.createApp(solver.name(), successfulTactic);
            app.tryToInstantiate(goal);
            goal.apply(app);
        }
    }

    @Override
    public void undo() {
        for (Node n : originalProofNodes) {
            n.proof().pruneProof(n);
        }
        Node node = originalSelectedNode;
        if (node == null) {
            throw new NullPointerException("No previously selected node to restore.");
        }
        mediator.getSelectionModel().setSelectedNode(node);
    }

    @Override
    public boolean canUndo() {
        Node node = originalSelectedNode;
        if (node == null) {
            throw new NullPointerException("No previously selected node to check.");
        }
        return goalsClosed.stream().allMatch(g -> proof.find(g.node())) && proof.find(node);
    }
}
