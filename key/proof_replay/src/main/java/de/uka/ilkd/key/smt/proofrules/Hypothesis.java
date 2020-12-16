package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class Hypothesis extends ProofRule {
    public Hypothesis(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // note: connected to lemma rule, see method replayLemma()
        Term hypothesis = extractRuleConclusion(ctx);

        if (replayVisitor.getHypoTaclets().get(hypothesis) == null) {
            throw new IllegalStateException("Hypothesis is not discharged by lemma rule: "
                + hypothesis);
        }
        NoPosTacletApp t = replayVisitor.getHypoTaclets().get(hypothesis);
        goal = goal.apply(t).head();

        // TODO: similar to asserted rule: more reasoning steps included (i.e. auto mode needed)?
        SequentFormula sf = ReplayTools.getLastAddedAntec(goal);
        goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "closeAntec", sf);
        return goal;
    }
}
