package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class AndElim extends ProofRule {
    public AndElim(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        final Term cutTerm = extractRuleAntecedents(ctx);
        final TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = ReplayTools.applyInteractive(goal, app).toList();
        Goal left = goals.get(1);
        final SequentFormula orig = left.sequent().succedent().get(0);

        SequentFormula rest = ReplayTools.getLastAddedAntec(left);
        ProofsexprContext lookUp = (ProofsexprContext) ReplayTools
            .ensureLookup(ctx.proofsexpr(0), replayVisitor);
        int arity = ReplayTools.ensureNoproofLookUp(extractRuleConclusionCtx(lookUp), replayVisitor).noproofterm().size() - 1;

        for (int i = 0; i < arity - 1; i++) {
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "andLeft", rest);
            rest = ReplayTools.getLastAddedAntec(left, 1);

            if (rest == null) {
                // attention: the formula may be equal to the original one by chance
                break;
            }
        }

        left = ReplayTools.applyNoSplitTopLevelSuc(left, "close", orig);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }
}
