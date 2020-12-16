package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class Symmetry extends ProofRule {
    public Symmetry(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // assumption: sequent only single formula in succedent (antecedent should be empty)
        // sequent: ==> A = B
        // TODO: we do not check that the premise of the rule is really the symmetric formula
        SequentFormula seqForm = goal.sequent().succedent().getFirst();
        Operator op = seqForm.formula().op();
        if (op == Equality.EQUALS) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "eqSymm", seqForm);
        } else if (op == Equality.EQV) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "equivSymm", seqForm);
        } else {
            throw new IllegalStateException("Operator not known to be symmetric: " + op);
        }
        replayRightSideHelper(ctx);
        return goal;
    }
}
