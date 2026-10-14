/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.actions.useractions;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.smt.SolverListenerF;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTFocusResults;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;

/**
 * User action to apply the results of running SMT solvers, FX port of
 * {@code de.uka.ilkd.key.gui.actions.useractions.SMTProofApplyUserAction} (Swing
 * SMTProofApplyUserAction.java:32-117): closes zero or more goals with the {@code SMTRule}
 * built-in rule (with the unsat core if available). The action is undoable: {@link #undo()}
 * prunes the proof back to the open goals recorded before the application (Swing
 * {@code SMTProofApplyUserAction.undo}) — the history mechanism of the Swing
 * {@code ActionHistoryExtension} records it through the mediator's user-action listeners
 * (WP-7).
 */
@NullMarked
public class SMTProofApplyUserActionF extends UserActionF {

    /**
     * Results of running the SMT solvers (one entry for each open goal).
     */
    private final Collection<SolverListenerF.InternSMTProblemF> smtProblems;

    /**
     * The number of goals that will be closed by this action.
     */
    private final int numberOfGoalsClosed;

    /**
     * The original nodes of the proof. Used to undo this action.
     */
    private final List<Node> originalProofNodes;

    private final Node originalSelectedNode;

    public SMTProofApplyUserActionF(KeYMediatorF mediator, Proof proof,
            Collection<SolverListenerF.InternSMTProblemF> smtProblems) {
        super(mediator, proof);
        this.smtProblems = smtProblems;
        this.numberOfGoalsClosed = (int) smtProblems.stream()
                .filter(p -> p.getSolver().getFinalResult().isValid() == ThreeValuedTruth.VALID)
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
        // Swing SolverListener.applyResults (SolverListener.java:209-221): the goal closing runs
        // with the interface frozen (stopInterface/startInterface); the FX counterpart is the
        // WP-1 auto-mode seam, and the default selection happens on unfreezing
        mediator.initiateAutoMode(proof, true, false);
        try {
            applyResults();
        } finally {
            mediator.finishAutoMode(proof, true, true, null);
        }
    }

    private void applyResults() {
        Collection<Goal> goalsClosed = new HashSet<>();
        // only close each solved goal once
        for (SolverListenerF.InternSMTProblemF problem : smtProblems) {
            Goal goal = problem.getProblem().getGoal();
            if (goalsClosed.contains(goal)
                    || problem.getSolver().getFinalResult().isValid() != ThreeValuedTruth.VALID) {
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
}
