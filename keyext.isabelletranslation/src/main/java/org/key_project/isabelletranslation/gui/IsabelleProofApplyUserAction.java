/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
import org.key_project.isabelletranslation.automation.IsabelleRuleApp;
import org.key_project.isabelletranslation.automation.IsabelleSolver;

public class IsabelleProofApplyUserAction extends UserAction {
    private final Collection<IsabelleSolver> solvers;

    private final Collection<Goal> goalsClosed = new HashSet<>();

    private final int numberOfGoalsClosed;

    private final Collection<Node> originalProofNodes;

    private final Node originalSelectedNode;

    public IsabelleProofApplyUserAction(KeYMediator mediator, Proof proof,
            Collection<IsabelleSolver> solvers) {
        super(mediator, proof);
        originalProofNodes = proof.openGoals().stream().map(Goal::node).toList();
        originalSelectedNode = mediator.getSelectedNode();
        this.solvers = solvers;
        this.numberOfGoalsClosed =
            (int) solvers.stream().filter(solver -> solver.getFinalResult().isSuccessful()).count();
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

            if (goalsClosed.contains(goal) || !solver.getFinalResult().isSuccessful()) {
                continue;
            }

            goalsClosed.add(goal);

            IBuiltInRuleApp app = IsabelleRuleApp.RULE.createApp(solver.name(),
                solver.getFinalResult().getSuccessfulTactic());
            app.tryToInstantiate(goal);
            goal.apply(app);
        }
    }

    @Override
    public void undo() {
        for (Node n : originalProofNodes) {
            n.proof().pruneProof(n);
        }
        mediator.getSelectionModel().setSelectedNode(originalSelectedNode);
    }

    @Override
    public boolean canUndo() {
        return goalsClosed.stream().allMatch(g -> proof.find(g.node()))
                && proof.find(originalSelectedNode);
    }
}
