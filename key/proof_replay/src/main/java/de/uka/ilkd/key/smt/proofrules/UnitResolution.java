package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.NotReplayableException;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.util.Pair;

import java.util.ArrayList;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class UnitResolution extends ProofRule {
    public UnitResolution(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        Term cutTerm;
        Term conclusion;
        try {
            conclusion = extractRuleConclusion(ctx);
            cutTerm = extractRuleAntecedents(ctx);
        } catch (NotReplayableException e) {
            e.printStackTrace();
            // if this branch is not replayable due to sorts problems:
            // TODO: collect and insert all assertions/hypotheses used in this subtree
            ReplayTools.runAutoMode(goal);
            return goal;
        }

        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = ReplayTools.applyInteractive(goal, app).toList();
        Goal left = goals.get(1);

        // first child is a | b | ...
        // last child is conclusion (maybe false)
        // others are unit clauses
        int unitClauseCount = ctx.proofsexpr().size() - 2;

        // two cases:
        // 1. conclusion is false (in this case we derive false in the antecedent)
        // 2. conclusion is literal (in this case we derive the conclusion from the first clause)
        if (conclusion.equals(services.getTermBuilder().ff())
            || conclusion.equals(services.getTermBuilder().FALSE())) {
            replayUnitResFalseHelper(left, unitClauseCount);
        } else {
            replayUnitResLiteralHelper(left, unitClauseCount, conclusion);
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }

    // unit resolution where the succedent is a literal that is not "false"
    private void replayUnitResLiteralHelper(Goal left, int unitClauseCount, Term conclusion) {
        SequentFormula seqForm = ReplayTools.getLastAddedAntec(left);    // = cut formula
        int literalCount = unitClauseCount + 1; // unit clauses and conclusion

        // split unit clauses from cutTerm, store them in list to find them again later
        List<SequentFormula> unitClauses = new ArrayList<>();
        for (int i = 0; i < unitClauseCount; i++) {
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "andLeft", seqForm);
            // conclusion should not be added to unit clause list
            //if (!ReplayTools.getLastAddedAntec(left).formula().equals(conclusion)) {
            unitClauses.add(ReplayTools.getLastAddedAntec(left, 0));
            //}
            seqForm = ReplayTools.getLastAddedAntec(left, 1);      // = rest of cut formula
        }

        // rest of original cut formula is the clause a | b | ... (contains all unit clauses)
        SequentFormula clause = seqForm;

        for (SequentFormula unitClause : unitClauses) {
            // bring unitClause to succedent
            if (isPosLiteral(unitClause.formula())) {           // apply notElimLeft
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "notElimLeft", unitClause);
            } else {                                            // apply notLeft
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "notLeft", unitClause);
            }
        }

        // BUGFIX: if the conclusion is itself a disjunction, the next rule application may fail!
        //  problem is flattening of nested or terms
        Pair<Integer, Goal> unfolded = unfoldDisjunctiveConclusion(left, conclusion);
        // unit clauses + unfolded conclusion
        literalCount = unitClauseCount + unfolded.first;
        left = unfolded.second;

        for (int i = 0; i < literalCount - 1; i++) {
            PosInTerm secondParam = PosInTerm.getTopLevel().down(1);
            left = ReplayTools.applyNoSplitPosAntec(left, "replace_known_right", secondParam,
                clause);
            clause = ReplayTools.getLastModifiedAntec(left);
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "concrete_or_4", clause);
            clause = ReplayTools.getLastModifiedAntec(left);
        }

        // replace last unit clause in clause
        left = ReplayTools.applyNoSplitTopLevelAntec(left, "replace_known_right", clause);
        clause = ReplayTools.getLastModifiedAntec(left);
        // last literal: clause = false now -> close branch
        left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeFalse", clause);
    }

    private Pair<Integer, Goal> unfoldDisjunctiveConclusion(Goal goal, Term conclusion) {
        if (conclusion.op() == Junctor.OR) {
            SequentFormula seqForm = findSequentFormulaForTerm(goal, conclusion, false);
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "orRight", seqForm);
            // subformulas may contain top level "or" again -> recursively unfold
            Pair<Integer, Goal> res0 = unfoldDisjunctiveConclusion(goal, conclusion.sub(0));
            Pair<Integer, Goal> res1 = unfoldDisjunctiveConclusion(res0.second, conclusion.sub(1));
            return new Pair<>(res0.first + res1.first, res1.second);
        }
        // do nothing
        return new Pair<>(1, goal);
    }

    // unit resolution where the succedent is "false"
    private void replayUnitResFalseHelper(Goal left, int unitClauseCount) {
        SequentFormula seqForm = ReplayTools.getLastAddedAntec(left);    // = cut formula

        // split unit clauses from cutTerm, store them in list to find them again later
        List<SequentFormula> unitClauses = new ArrayList<>();
        for (int i = 0; i < unitClauseCount; i++) {
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "andLeft", seqForm);
            //unitClauses.add(ReplayTools.getLastAddedAntec(left));
            unitClauses.add(ReplayTools.getLastAddedAntec(left, 0));
            seqForm = ReplayTools.getLastAddedAntec(left, 1);      // = rest of cut formula
        }

        // rest of original cut formula is the clause a | b | ... (contains all unit clauses)
        SequentFormula clause = seqForm;

        for (SequentFormula unitClause : unitClauses) {
            // bring unitClause to succedent
            if (isPosLiteral(unitClause.formula())) {           // apply notElimLeft
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "notElimLeft", unitClause);
            } else {                                            // apply notLeft
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "notLeft", unitClause);
            }
        }
        // note: two separate loops since order may differ
        for (int i = 0; i < unitClauseCount; i++) {
            if (i == unitClauseCount - 1) {
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "replace_known_right", clause);
            } else {
                // replace last unit clause in clause
                PosInTerm secondParam = PosInTerm.getTopLevel().down(1);
                left = ReplayTools.applyNoSplitPosAntec(left, "replace_known_right", secondParam,
                    clause);
            }
            clause = ReplayTools.getLastModifiedAntec(left);

            if (i == unitClauseCount - 1) {
                // last unit clause: clause = false now -> close branch
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeFalse", clause);
            } else {
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "concrete_or_4", clause);
                clause = ReplayTools.getLastModifiedAntec(left);
            }
        }
    }

    private boolean isPosLiteral(Term formula) {
        return formula.op() != Junctor.NOT;
    }
}
