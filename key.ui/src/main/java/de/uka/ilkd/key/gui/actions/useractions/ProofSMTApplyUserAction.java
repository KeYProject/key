/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.SMTRuleApp;

import org.key_project.util.collection.ImmutableList;

/**
 * User action to apply the results of running SMT solvers.
 * Closes zero or more goals.
 *
 * @author Arne Keller
 */
public class ProofSMTApplyUserAction extends UserAction {
    /**
     * Results of running the SMT solvers (one entry for each open goal).
     */
    private final Collection<SolverListener.InternSMTProblem> smtProblems;
    /**
     * The nodes closed by applying this action.
     * Populated in {@link #apply()}.
     */
    private final Collection<Goal> goalsClosed = new HashSet<>();
    /**
     * The number of goals that will be closed by this action.
     */
    private final int numberOfGoalsClosed;

    public ProofSMTApplyUserAction(KeYMediator mediator, Proof proof,
            Collection<SolverListener.InternSMTProblem> smtProblems) {
        super(mediator, proof);
        this.smtProblems = smtProblems;
        this.numberOfGoalsClosed = (int) smtProblems.stream()
                .filter(p -> p.getProblem().getFinalResult()
                        .isValid() == SMTSolverResult.ThreeValuedTruth.VALID)
                .count();
    }

    @Override
    public String name() {
        return String.format("Close: %d goals by SMT", numberOfGoalsClosed);
    }

    @Override
    protected void apply() {
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
                app = SMTRuleApp.RULE.createApp(problem.getSolver().name(), unsatCore);
            } else {
                app = SMTRuleApp.RULE.createApp(problem.getSolver().name());
            }
            app.tryToInstantiate(goal);
            goal.apply(app);
        }
    }

    @Override
    public void undo() {
        for (Goal g : goalsClosed) {
            Node n = g.node();
            n.setAppliedRuleApp(null);
            // re-open the goal
            Goal firstGoal = proof.getClosedGoal(n);
            proof.reOpenGoal(firstGoal);
        }
    }

    @Override
    public boolean canUndo() {
        return goalsClosed.stream().allMatch(g -> proof.find(g.node()));
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
