package org.key_project.isabelletranslation.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.useractions.UserAction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTRuleApp;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.automation.IsabelleSolver;

import java.util.Collection;
import java.util.HashSet;

public class ProofApplyUserAction extends UserAction {
    private final Collection<IsabelleSolver> solvers;

    private final Collection<Goal> goalsClosed = new HashSet<>();

    private final int numberOfGoalsClosed;

    public ProofApplyUserAction(KeYMediator mediator, Proof proof,
                                Collection<IsabelleSolver> solvers) {
        super(mediator, proof);
        this.solvers = solvers;
        this.numberOfGoalsClosed = (int) solvers.stream().filter(solver ->
                solver.getFinalResult().isSuccessful()).count();
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

            //TODO SMTRuleApp does not serve any purpose as a SMT exclusive rule.
            //  The documentation does not suggest it should only be used for SMT, yet the name would suggest this.
            //  Changing this requires changing parts of the KeY core. This needs a different class, which does not prepend "SMT" to all titles
            IBuiltInRuleApp app = SMTRuleApp.RULE.createApp("")
                    .setTitle("Isabelle: " + solver.getFinalResult().getSuccessfulTactic());
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
}
