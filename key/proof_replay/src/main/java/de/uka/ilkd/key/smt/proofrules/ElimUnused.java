package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTProofParser;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class ElimUnused extends ProofRule {
    public ElimUnused(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {

        if (ctx.rulename == null || !ctx.rulename.getText().equals("elim-unused")) {
            throw new IllegalStateException("Invalid 'elim-unused' rule found!");
        }

        NoprooftermContext eq = ReplayTools.ensureNoproofLookUp(ctx.proofsexpr(0), replayVisitor);

        // eq.noproofterm(0) is '=' or 'iff'
        NoprooftermContext left = eq.noproofterm(1);
        int leftVarCount = calcBoundVarsLeft(left);
        NoprooftermContext right = eq.noproofterm(2);
        int rightVarCount = calcBoundVarsLeft(right);

        SequentFormula seqForm = goal.sequent().succedent().getFirst();

        int eliminatedVars = leftVarCount - rightVarCount;
        for (int i = 0; i < eliminatedVars; i++) {
            // all_unused on subterm:

            // prepare position: left side of equality ...
            PosInTerm pit = PosInTerm.getTopLevel().down(0);
            for (int j = 0; j < rightVarCount; j++) {
                // ... and skip top level quantifier(s)
                pit = pit.down(0);
            }
            goal = ReplayTools.applyNoSplitPosSuc(goal, "all_unused", pit, seqForm);
            seqForm = ReplayTools.getLastModifiedSuc(goal);
        }

        // eq_eq
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "eq_eq", seqForm);

        // closeTrue
        seqForm = ReplayTools.getLastModifiedSuc(goal);
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "closeTrue", seqForm);

        //assert goal.node().isClosed();
        return null;
    }

    // determine count of variables bound by top level 'forall' quantifier
    private int calcBoundVarsLeft(NoprooftermContext ctx) {
        NoprooftermContext lookup = ReplayTools.ensureNoproofLookUp(ctx, replayVisitor);
        if (lookup.quant == null || !lookup.quant.getText().equals("forall")) {
            return 0;
        }
        return lookup.sorted_var().size();
    }
}
