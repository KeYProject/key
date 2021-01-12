package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class ThLemma extends ProofRule {
    public ThLemma(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        int arity = ctx.proofsexpr().size();

        // two cases: leaf rule or intermediate rule in proof
        if (ctx.proofsexpr(arity - 1).getText().equals("false")) {
            // intermediate rule (works together with lemma/hypothesis)
            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();

            Goal left = goals.get(1);
            ReplayTools.runAutoMode(left);
            //assert left.node().isClosed();

            ////////////////////////////////////////////////////////////////////////////////////////

            goal = goals.get(0);
            replayRightSideHelper(ctx);
        } else {
            // leaf rule
            ReplayTools.runAutoMode(goal);
        }
        return goal;
    }
}
