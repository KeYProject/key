/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.*;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/**
 * User action to apply the results of running SMT solvers.
 * Closes zero or more goals.
 *
 * @author Arne Keller
 */
public class SMTProofApplyUserAction extends UserAction {
    /**
     * Results of running the SMT solvers (one entry for each open goal).
     */
    private final Collection<SolverListener.InternSMTProblem> smtProblems;
    /**
     * The number of goals that will be closed by this action.
     */
    private final int numberOfGoalsClosed;
    /**
     * The original nodes of the proof. Used to undo this action
     */
    private final Collection<Node> originalProofNodes;

    private final Node originalSelectedNode;

    public SMTProofApplyUserAction(KeYMediator mediator, Proof proof,
            Collection<SolverListener.InternSMTProblem> smtProblems) {
        super(mediator, proof);
        this.smtProblems = smtProblems;
        this.numberOfGoalsClosed = (int) smtProblems.stream()
                .filter(p -> p.getProblem().getFinalResult()
                        .isValid() == SMTSolverResult.ThreeValuedTruth.VALID)
                .count();
        this.originalProofNodes = proof.openGoals().stream().map(Goal::node).toList();
        this.originalSelectedNode = mediator.getSelectedNode();
    }

    @Override
    public String name() {
        return String.format("Close: %d goals by SMT", numberOfGoalsClosed);
    }

    @Override
    protected void apply() {
        Collection<Goal> goalsClosed = new HashSet<>();
        // only close each solved goal once
        for (SolverListener.InternSMTProblem problem : smtProblems) {
            Goal goal = problem.getProblem().getGoal();
            if (goalsClosed.contains(goal)
                    || problem.getSolver().getFinalResult()
                            .isValid() != SMTSolverResult.ThreeValuedTruth.VALID) {
                continue;
            }
            goalsClosed.add(goal);
            ImmutableList<PosInOccurrence> unsatCore =
                SMTFocusResults.getUnsatCore(problem.getProblem());
            IBuiltInRuleApp app;
            if (unsatCore != null) {
                app = SMTRule.INSTANCE.createApp(problem.getSolver().name(), unsatCore);
            } else {
                app = SMTRule.INSTANCE.createApp(problem.getSolver().name());
            }
            app = AbstractProofControl.completeBuiltInRuleAppByDefault(app, goal, false);
            if (app == null) {
                // should be unreachable under normal circumstances
                throw new RuntimeException("Could not instantiate SMT Rule Application");
            }
            goal.apply(app);
        }
    }

    @Override
    public void undo() {
        for (Node n : originalProofNodes) {
            proof.pruneProof(n);
        }
        mediator.getSelectionModel().setSelectedNode(originalSelectedNode);
    }

    @Override
    public boolean canUndo() {
        return originalProofNodes.stream().allMatch(proof::find);
    }

    private String getTitle(SMTProblem p) {
        StringBuilder title = new StringBuilder();
        Iterator<SMTSolver> it = p.getSolvers().iterator();
        while (it.hasNext()) {
            title.append(it.next().name());
            if (it.hasNext()) {
                title.append(", ");
            }
        }
        return title.toString();
    }
}
