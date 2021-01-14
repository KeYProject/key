package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class IffFalse extends ProofRule {
    public IffFalse(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        SequentFormula seqForm = goal.sequent().succedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp concreteEq4 = ReplayTools.createTacletApp("concrete_eq_4", pio, goal);
        goal = ReplayTools.applyInteractive(goal, concreteEq4).head();
        continueReplay(ctx.proofsexpr(0));
        return goal;
    }
}
