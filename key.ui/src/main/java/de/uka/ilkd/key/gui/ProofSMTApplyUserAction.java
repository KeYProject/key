package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;

public class ProofSMTApplyUserAction extends UserAction {
    private final Collection<SMTProblem> smtProblems;
    private final Collection<Node> goalsClosed = new ArrayList<>();

    public ProofSMTApplyUserAction(KeYMediator mediator, Proof proof,
            Collection<SMTProblem> smtProblems) {
        super(mediator, proof);
        this.smtProblems = smtProblems;
    }

    @Override
    public String name() {
        return String.format("Close: %d goals by SMT", smtProblems.size());
    }

    @Override
    public void apply() {
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

    private String getTitle(SMTProblem p) {
        String title = "";
        Iterator<SMTSolver> it = p.getSolvers().iterator();
        while (it.hasNext()) {
            title += it.next().name();
            if (it.hasNext()) {
                title += ", ";
            }
        }
        return title;
    }
}
