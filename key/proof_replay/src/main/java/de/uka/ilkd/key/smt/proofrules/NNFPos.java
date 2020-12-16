package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

import java.util.List;

public class NNFPos extends ProofRule {
    public NNFPos(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        Term antecedent = extractRuleAntecedents(ctx);
        TacletApp cutApp = ReplayTools.createCutApp(goal, antecedent);
        List<Goal> goals = goal.apply(cutApp).toList();
        Goal left = goals.get(1);

        // currently we run auto mode for converting to nnf
        ReplayTools.runAutoMode(left);
        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }
}
