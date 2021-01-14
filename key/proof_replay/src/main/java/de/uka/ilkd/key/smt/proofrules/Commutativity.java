package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTProofParser;

import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class Commutativity extends ProofRule {
    public Commutativity(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // to be safe here: cut with antecendent and run auto mode, since we do not know which
        // operator is used
        Term cutTerm = extractRuleAntecedents(ctx);

        TacletApp cutApp = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = ReplayTools.applyInteractive(goal, cutApp).toList();
        Goal left = goals.get(1);

        ReplayTools.runAutoModePropositional(left, 1000);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }
}
