package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class ModusPonens extends ProofRule {
    public ModusPonens(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = ReplayTools.applyInteractive(goal, app).toList();

        ////////////////////////////////////////////////////////////////////////////////////////////
        // left: and_left, replace_known_left, concrete_impl, close
        Goal left = goals.get(1);

        SequentFormula seqForm = ReplayTools.getLastAddedAntec(left);
        left = ReplayTools.applyNoSplitTopLevelAntec(left, "andLeft", seqForm);

        seqForm = ReplayTools.getLastAddedAntec(left);
        left = ReplayTools.applyNoSplitPosAntec(left, "replace_known_left",
            PosInTerm.getTopLevel().down(0), seqForm);

        seqForm = ReplayTools.getLastModifiedAntec(left);
        left = ReplayTools.applyNoSplitTopLevelAntec(left, "concrete_eq_1", seqForm);

        // Two cases: Is the last changed formula "false" or not?
        SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
        FormulaChangeInfo fci = sci.modifiedFormulas(true).head();
        // bugfix: NPE if sequence is: a, a <-> a ==> a
        //Term newTerm = fci.getNewFormula().formula();
        if (fci != null && fci.getNewFormula().formula().equals(services.getTermBuilder().ff())) {
            // 1. case: Gamma, false ==> Delta
            //   in this case apply closeFalse (used for final refutation of proof)
            seqForm = ReplayTools.getLastModifiedAntec(left);
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeFalse", seqForm);
        } else {
            // 2. case: Gamma, f ==> Delta, f
            //   in this case apply closeAntec
            seqForm = ReplayTools.getLastModifiedAntec(left);
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
        }

        assert left.node().isClosed();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }
}
