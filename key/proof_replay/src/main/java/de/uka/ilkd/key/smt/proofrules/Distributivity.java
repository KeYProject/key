package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class Distributivity extends ProofRule {
    public Distributivity(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // TODO: restrict to specific rules? better "manual" replay?
        ReplayTools.runAutoModePropositional(goal, 1000);
        return goal;
    }
}
