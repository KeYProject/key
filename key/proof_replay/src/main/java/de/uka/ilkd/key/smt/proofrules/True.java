package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class True extends ProofRule {
    public True(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // assumption: sequent only single formula in succedent (antecedent should be empty)
        SequentFormula seqForm = goal.sequent().succedent().getFirst();
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "closeTrue", seqForm);
        return goal;
    }
}
