package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class DefAxiom extends ProofRule {
    public DefAxiom(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // closing rule (Tseitin axioms)
        // quick and dirty solution: use auto mode (simple propositional steps)
        // TODO: implement schemas
        ReplayTools.runAutoModePropositional(goal, 50);
        return goal;
    }
}
