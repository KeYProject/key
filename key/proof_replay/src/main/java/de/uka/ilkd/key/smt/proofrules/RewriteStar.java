package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class RewriteStar extends ProofRule {
    public RewriteStar(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // this rule should not be used except with CONTEXT_SIMPLIFIER=true or BIT2BOOL=true
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = ReplayTools.applyInteractive(goal, app).toList();
        Goal left = goals.get(1);

        // close this goal by auto mode
        ReplayTools.runAutoModePropositional(left, 1000);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }
}
