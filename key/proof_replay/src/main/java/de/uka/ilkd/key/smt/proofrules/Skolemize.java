package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.DefCollector;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTProofParser;

import java.util.ArrayList;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class Skolemize extends ProofRule {
    public Skolemize(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        SequentFormula conclusion = goal.sequent().succedent().getFirst();
        ProofsexprContext equiSat = ctx.proofsexpr(0);
        // collect all positions of the quantified variable in lhs term
        // <-> positions of ifEx term in right hand side formula
        SMTProofParser.NoprooftermContext lhsCtx = equiSat.noproofterm().noproofterm(1);
        DefCollector defCollector = new DefCollector(replayVisitor.getSmtReplayer(), services,
                                                     replayVisitor.getSkolemSymbols());
        Term lhs = defCollector.visit(lhsCtx);

        // lhs is either ex ... or !all ... now
        List<PosInTerm> pits;
        PosInTerm pit;
        PosInTerm ifEx;
        if (lhs.op() == Quantifier.EX) {
            pits = collectQvPositions(lhs);
            assert !pits.isEmpty();
            // right side of equiv
            pit = pits.get(0);
            // prepend 1 (i.e. select ride side of equiv) to found position
            ifEx = PosInTerm.getTopLevel().down(1);
            for (int i = 0; i < pit.depth(); i++) {
                ifEx = ifEx.down(pit.getIndexAt(i));
            }
            // ifEx points to first ifEx term in conclusion now
            goal = ReplayTools.applyNoSplitPosSuc(goal, "epsDefAdd", ifEx, conclusion);

            // taclet epsDefAdd adds the same formula as conclusion on the right side -> close
            SequentFormula sf = ReplayTools.getLastAddedAntec(goal);
            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "closeAntec", sf);
            // goal is closed now!
        } else if (lhs.op() == Junctor.NOT && !lhs.subs().isEmpty()
            && lhs.sub(0).op() == Quantifier.ALL) {
            pits = collectQvPositions(lhs.sub(0));
            assert !pits.isEmpty();
            // right side of equiv
            pit = pits.get(0);
            // prepend 1 (i.e. select ride side of equiv) to found position
            ifEx = PosInTerm.getTopLevel().down(1).down(0);             // additional "not" to skip

            for (int i = 0; i < pit.depth(); i++) {
                ifEx = ifEx.down(pit.getIndexAt(i));
            }
            // ifEx points to first ifEx term in conclusion now
            goal = ReplayTools.applyNoSplitPosSuc(goal, "epsDefAdd", ifEx, conclusion);

            // nnf-notAll
            PosInTerm notAllPos = PosInTerm.getTopLevel().down(0);
            goal = ReplayTools.applyNoSplitPosSuc(goal, "nnf_notAll", notAllPos, conclusion);

            // taclet epsDefAdd adds the same formula as conclusion on the right side -> close
            SequentFormula sf = ReplayTools.getLastModifiedSuc(goal);
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "close", sf);
            // goal is closed now!
        } else {
            throw new IllegalStateException("In sk rule, ex or not all is expected!");
        }
        return goal;
    }

    private List<PosInTerm> collectQvPositions(Term quant) {
        QuantifiableVariable qv = quant.boundVars().last(); // TODO: there has to be exactly one!
        return collectQvPositionsRec(qv, quant.sub(0), PosInTerm.getTopLevel());
    }

    private List<PosInTerm> collectQvPositionsRec(QuantifiableVariable qv,
                                                    Term subTerm, PosInTerm prefix) {
        List<PosInTerm> result = new ArrayList<>();
        if (subTerm.op() instanceof QuantifiableVariable
            && ReplayTools.equalsOp((QuantifiableVariable) subTerm.op(), qv)) {
            result.add(prefix);
        } else {
            for (int i = 0; i < subTerm.subs().size(); i++) {
                // TODO: fix: we must not descend if there is a binder binding a variable with the
                //  same name and sort (this variable is shadowing qv)
                Term sub = subTerm.sub(i);
                /* what was the purpose of this?
                if (sub.op().equals(IfExThenElse.IF_EX_THEN_ELSE)) {
                    System.out.println();
                    //continue;
                } else if (sub.op() instanceof Quantifier) {
                    System.out.println();
                    //continue;
                }*/
                List<PosInTerm> subPos = collectQvPositionsRec(qv, sub, prefix.down(i));
                result.addAll(subPos);
            }
        }
        return result;
    }
}
