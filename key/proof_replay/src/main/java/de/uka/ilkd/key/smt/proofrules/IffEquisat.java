package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ReplayVisitor;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class IffEquisat extends ProofRule {
    public IffEquisat(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // TODO is this correct?
        // nothing to do here, since we replace all ~ using <-> and epsilon when building terms
        // directly descend into antecedent
        replayRightSideHelper(ctx);
        return goal;
    }
}
