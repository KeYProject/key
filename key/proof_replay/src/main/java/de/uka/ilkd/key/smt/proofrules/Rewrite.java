package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class Rewrite extends ProofRule {
    public Rewrite(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        if (goal.sequent().succedent().get(0).formula().op() == Equality.EQV) {
            // equiv_right top level to guide the prover
            SequentFormula seqForm = goal.sequent().succedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            TacletApp app = ReplayTools.createTacletApp("equiv_right", pio, goal);
            List<Goal> goals = ReplayTools.applyInteractive(goal, app).toList();
            // running automode separately on both goals increases success rate
            ReplayTools.runAutoMode(goals.get(0));
            ReplayTools.runAutoMode(goals.get(1));
        } else {
            ReplayTools.runAutoMode(goal);
        }
        return goal;
    }
}
