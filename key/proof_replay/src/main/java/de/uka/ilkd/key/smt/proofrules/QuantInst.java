package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.DefCollector;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTProofParser;

import java.util.LinkedList;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class QuantInst extends ProofRule {
    public QuantInst(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // should be: orRight, notRight, instAll, close
        SequentFormula seqForm = goal.sequent().succedent().getFirst();

        // TODO: real problem is n-ary vs nested or here
        // TODO: "conclusion" (right side of quantifier) may be of following form,
        //  where | is left-associative!
        // !(forall ...) | a | b | c

        // while top level is |:
        //      orRight
        List<SequentFormula> conclusionSubs = new LinkedList<>();
        while (seqForm.formula().op() == Junctor.OR) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "orRight", seqForm);
            seqForm = ReplayTools.getLastAddedSuc(goal, 1);
            conclusionSubs.add(ReplayTools.getLastAddedSuc(goal, 0));
        }

        // now seqForm is the term !(forall ...)
        // notRight
        SequentFormula all = ReplayTools.getLastAddedSuc(goal, 1);
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "notRight", all);

        int instVarCount = extractInstVarCount(ctx);

        for (int i = 0; i < instVarCount; i++) {
            // allLeft
            seqForm = ReplayTools.getLastAddedAntec(goal);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            System.out.println("Creating TacletApp allLeft");
            TacletApp app = ReplayTools.createTacletApp("allLeft", pio, goal);
            SchemaVariable qvSv = app.uninstantiatedVars().iterator().next();
            Term allInst = extractQuantifierInstantiation(ctx, i);

            // TODO: hopefully, these lines are never needed...
            // fix: allInst may have formula sort (with = TRUE)
            if (allInst.sort() == Sort.FORMULA) {
                if (allInst.op() == Equality.EQUALS) {
                    Term subL = allInst.sub(0);
                    Term subR = allInst.sub(1);
                    allInst = (subL.op() == Junctor.TRUE) ? subR : subL;
                    app = app.addInstantiation(qvSv, allInst, true, services);
                    goal = goal.apply(app).head();

                    // in this case, the formulas have different structures -> first order auto mode,
                    // closeable without additional quantifier instantiation
                    ReplayTools.runAutoModeFirstOrder(goal, 50);
                    // goal is closed now
                    return goal;
                }
                // TODO: don't know what to do better here
                ReplayTools.runAutoModeFirstOrder(goal, 50);
                // hopefully, the goal is closed now
                return goal;
            }

            app = app.addInstantiation(qvSv, allInst, true, services);
            goal = goal.apply(app).head();
        }

        // replace_known_right + concrete_or_4 on a, b, c
        seqForm = ReplayTools.getLastAddedAntec(goal);
        PosInTerm pit = PosInTerm.getTopLevel().down(1);    // right side of "or"
        for (int i = 0; i < conclusionSubs.size() - 1; i++) {
            goal = ReplayTools.applyNoSplitPosAntec(goal, "replace_known_right", pit, seqForm);
            seqForm = ReplayTools.getLastModifiedAntec(goal);

            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_or_4", seqForm);
            seqForm = ReplayTools.getLastModifiedAntec(goal);
        }
        // last literal of conclusion (has different position)
        pit = PosInTerm.getTopLevel();
        goal = ReplayTools.applyNoSplitPosAntec(goal, "replace_known_right", pit, seqForm);

        // closeFalse
        seqForm = ReplayTools.getLastModifiedAntec(goal);
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "closeFalse", seqForm);
        // goal is closed now!
        return goal;
    }

    private int extractInstVarCount(ProofsexprContext ctx) {
        ProofsexprContext conclusionCtx = extractRuleConclusionCtx(ctx);
        // conclusionCtx should be: (or (not (forall (x) (P x))) (P a))
        SMTProofParser.NoprooftermContext or = ReplayTools
            .ensureNoproofLookUp(conclusionCtx.noproofterm(), replayVisitor);
        SMTProofParser.NoprooftermContext notAll = ReplayTools
            .ensureNoproofLookUp(or.noproofterm(1), replayVisitor);
        SMTProofParser.NoprooftermContext all = ReplayTools
            .ensureNoproofLookUp(notAll.noproofterm(1), replayVisitor);
        SMTProofParser.NoprooftermContext matrix = ReplayTools
            .ensureNoproofLookUp(all.noproofterm(0), replayVisitor);
        return all.sorted_var().size();
    }

    private Term extractQuantifierInstantiation(ProofsexprContext quantInstCtx, int varIndex) {
        ProofsexprContext conclusionCtx = extractRuleConclusionCtx(quantInstCtx);
        // conclusionCtx should be: (or (not (forall (x) (P x))) (P a))
        SMTProofParser.NoprooftermContext or = ReplayTools
            .ensureNoproofLookUp(conclusionCtx.noproofterm(), replayVisitor);
        SMTProofParser.NoprooftermContext notAll = ReplayTools
            .ensureNoproofLookUp(or.noproofterm(1), replayVisitor);
        SMTProofParser.NoprooftermContext all = ReplayTools
            .ensureNoproofLookUp(notAll.noproofterm(1), replayVisitor);
        SMTProofParser.NoprooftermContext matrix = ReplayTools
            .ensureNoproofLookUp(all.noproofterm(0), replayVisitor);

        String varName = all.sorted_var(varIndex).SYMBOL().getText();
        List<Integer> pos = ReplayTools.extractPosition(varName, matrix);

        assert pos != null && pos.size() >= 1;

        // (or (not (all (or a b c))) a' b' c')
        // pos contains position of bound variable inside (or a b c), but we are interested in
        // position inside (or ... a' b' c') -> skip notAll (first child of or)

        if (or.noproofterm().size() > 3) {  // 3: "or" + notAll + a
            //if (matrix.func != null && matrix.func.getText().equals("or")) {
            pos.set(0, pos.get(0) + 2);     // + 2: skip "or" and skip notAll subterm

            // position in the top level "or" has been merged into pos[0]
            pos.remove(1);
        } else {
            // (or (not (all a))) a')
            pos.add(0, 2);      // descend into a'
            //pos.set(0, pos.get(0) + 1);     // TODO: ??? but seems to work
        }

        SMTProofParser.NoprooftermContext inst = or;
        for (Integer i : pos) {
            // fix: each subterm could be a symbol bound by let -> lookup first
            inst = ReplayTools.ensureNoproofLookUp(inst, replayVisitor).noproofterm(i);
        }

        // now convert instantiation to KeY term
        return inst.accept(new DefCollector(replayVisitor.getSmtReplayer(), services));
    }
}
