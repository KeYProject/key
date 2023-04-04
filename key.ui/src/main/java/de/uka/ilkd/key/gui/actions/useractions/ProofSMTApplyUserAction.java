package de.uka.ilkd.key.gui.actions.useractions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;

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
    private final Collection<SMTProblem> smtProblems;
    /**
     * The nodes closed by applying this action.
     * Populated in {@link #apply()}.
     */
    private final Collection<Node> goalsClosed = new ArrayList<>();
    /**
     * The number of goals that will be closed by this action.
     */
    private final int numberOfGoalsClosed;

    public ProofSMTApplyUserAction(KeYMediator mediator, Proof proof,
            Collection<SMTProblem> smtProblems) {
        super(mediator, proof);
        this.smtProblems = smtProblems;
        this.numberOfGoalsClosed = (int) smtProblems.stream()
                .filter(p -> p.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID)
                .count();
    }

    @Override
    public String name() {
        return String.format("Close: %d goals by SMT", numberOfGoalsClosed);
    }

    @Override
    protected void apply() {
        for (SMTProblem problem : smtProblems) {
            if (problem.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID) {
                IBuiltInRuleApp app =
                    RuleAppSMT.rule.createApp(null).setTitle(getTitle(problem));
                goalsClosed.add(problem.getGoal().node());
                problem.getGoal().apply(app);
            }
        }
    }

    @Override
    public void undo() {
        for (Node n : goalsClosed) {
            n.setAppliedRuleApp(null);
            // re-open the goal
            Goal firstGoal = proof.getClosedGoal(n);
            proof.add(firstGoal);
            proof.reOpenGoal(firstGoal);
        }
    }

    @Override
    public boolean canUndo() {
        return goalsClosed.stream().allMatch(proof::find);
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
