package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class Reflexivity extends ProofRule {
    public Reflexivity(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // assumption: sequent only single formula in succedent (antecedent should be empty)
        // sequent: ==> A = A     or     ==> A <-> A
        SequentFormula seqForm = goal.sequent().succedent().getFirst();
        if (seqForm.formula().op() == Equality.EQUALS) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "eqClose", seqForm);
        } else if (seqForm.formula().op() == Equality.EQV) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "eq_eq", seqForm);
        } else {
            throw new IllegalStateException("Top level operator should be = or <-> but is "
                + seqForm.formula().op());
        }
        seqForm = ReplayTools.getLastModifiedSuc(goal);
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "closeTrue", seqForm);
        // goal is closed now!
        return goal;
    }
}
