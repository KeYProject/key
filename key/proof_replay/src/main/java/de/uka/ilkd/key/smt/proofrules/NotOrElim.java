package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class NotOrElim extends ProofRule {
    public NotOrElim(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // notLeft, orRight ..., notRight, ..., closeAntec
        final Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = ReplayTools.applyInteractive(goal, app).toList();
        Goal left = goals.get(1);
        final SequentFormula rhs = left.sequent().succedent().get(0);
        SequentFormula seqForm = ReplayTools.getLastAddedAntec(left);

        // to avoid cases where a temporary formula is equal to the conclusion
        // (and thus destroying all index calculations), we hide the original rhs here
        left = ReplayTools.applyNoSplitTopLevelSuc(left, "hide_right", rhs);
        NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();

        left = ReplayTools.applyNoSplitTopLevelAntec(left, "notLeft", seqForm);

        seqForm = ReplayTools.getLastAddedSuc(left);

        // TODO: better count up to arity, however, extracting the original SMT arity of "or" is
        //  pretty difficult
        //  pragmatic solution: will always find the searched literal
        //int arity = extractOrArity(ctx.proofsexpr(0));
        //for (int i = 0; i < arity; i++) {
        while (seqForm.formula().op() == Junctor.OR) {

            left = ReplayTools.applyNoSplitTopLevelSuc(left, "orRight", seqForm);

            seqForm = ReplayTools.getLastAddedSuc(left, 1);
            SequentFormula split = ReplayTools.getLastAddedSuc(left, 0);

            if (split.formula().op() == Junctor.NOT) {
                left = ReplayTools.applyNoSplitTopLevelSuc(left, "notRight", split);
            } else {
                left = ReplayTools.applyNoSplitTopLevelSuc(left, "notElimRight", split);
            }

            // early close if possible
            split = ReplayTools.getLastAddedAntec(left);
            if (split.formula().equals(rhs.formula())) {
                // found the literal -> close
                // reinsert original rhs
                left = ReplayTools.applyInteractive(left, insertRule).head();
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", split);
                break;
            } else if (ReplayTools.eqDifferentPolarity(seqForm, rhs)) {
                // additional check necessary for pragmatic solution, see e.g. sequent
                // !((p | q) | p) ==> !(p | q)
                if (seqForm.formula().op() == Junctor.NOT) {
                    left = ReplayTools.applyInteractive(left, insertRule).head();
                    left = ReplayTools.applyNoSplitTopLevelAntec(left, "notRight", seqForm);
                    seqForm = ReplayTools.getLastAddedAntec(left);
                    left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
                } else if (rhs.formula().op() == Junctor.NOT) {
                    left = ReplayTools.applyInteractive(left, insertRule).head();
                    left = ReplayTools.applyNoSplitTopLevelAntec(left, "notElimRight", seqForm);
                    seqForm = ReplayTools.getLastAddedAntec(left);
                    left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
                }
            }
        }

        if (!left.node().isClosed()) {
            if (seqForm.formula().op() == Junctor.NOT) {
                left = ReplayTools.applyNoSplitTopLevelSuc(left, "notRight", seqForm);
            } else {
                left = ReplayTools.applyNoSplitTopLevelSuc(left, "notElimRight", seqForm);
            }
            seqForm = ReplayTools.getLastAddedAntec(left);
            // now closing must be possible (or there is something wrong)
            // reinsert original rhs
            left = ReplayTools.applyInteractive(left, insertRule).head();

            seqForm = ReplayTools.getLastAddedSuc(left);
            left = ReplayTools.applyNoSplitTopLevelSuc(left, "close", seqForm);
            //left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }
}
