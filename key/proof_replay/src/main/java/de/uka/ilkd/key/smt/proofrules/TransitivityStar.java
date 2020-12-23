package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class TransitivityStar extends ProofRule {
    public TransitivityStar(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        // trans* rule contains multiple transitivity and symmetry steps,
        // therefore we need auto mode here (however, should be really simple to close)
        ReplayTools.runAutoModePropositional(goal, 1000);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }
}
