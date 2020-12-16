package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTProofParser;

import java.util.Map;

public class Asserted extends ProofRule {
    public Asserted(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(SMTProofParser.ProofsexprContext ctx) {
        // get sequentFormula, get corresponding insert_taclet from map, apply
        SequentFormula seqForm = goal.sequent().succedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);

        // two possible choices:
        TacletApp app = replayVisitor.getSmtReplayer().getInsertTacletForSF(seqForm);
        Term negTerm = services.getTermBuilder().not(seqForm.formula());

        // fix: we need the exact SequentFormula instance!
        //SequentFormula negForm = new SequentFormula(negTerm);
        SequentFormula negForm = findSequentFormulaForTerm(goal, negTerm);

        TacletApp notApp = replayVisitor.getSmtReplayer().getInsertTacletForSF(negForm);

        if (app != null) {
            goal = goal.apply(app).head();
        } else if (notApp != null) {
            goal = goal.apply(notApp).head();

            if (seqForm.formula().op() == Junctor.NOT) {
                app = ReplayTools.createTacletApp("notRight", pio, goal);
                goal = goal.apply(app).head();

                SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
                SequentFormula addedAntec = sci.addedFormulas(true).head();
                pio = new PosInOccurrence(addedAntec, PosInTerm.getTopLevel(), true);
                app = ReplayTools.createTacletApp("closeAntec", pio, goal);
                goal = goal.apply(app).head();
            }
        } else {
            //throw new IllegalStateException("The formula " + seqForm.formula() + " is not an assertion!");
            System.out.println("The formula " + seqForm.formula() + " is not found as assertion!");
            //System.out.println("Starting auto mode ...");
            // TODO: insert matching assertion (how to find?)
            // TODO: we need a more general solution here: what if the rule refers to an assertion
            //  that does not stem from the sequent, but e.g. from the type axioms?
            // Note: this is a problem if assertions are rewritten (we hope that this does not
            // happpen, or else we will not be able to find them)

            // there is no taclet app found (e.g. for type hierarchy axioms)
            ReplayTools.runAutoMode(goal);

            if (!goal.node().isClosed()) {
                // still not closed -> seems to be an assertion from sequent which we did not find,
                // to be sure we add all assertions and hypotheses and run TryCloseMacro again

                goal = insertAllAssertions(goal);
                goal = insertAllHypotheses(goal);
                ReplayTools.runAutoMode(goal);

                // goal should be closed now; if not, something really has gone wrong!
            }
        }
        return goal;
    }

    private Goal insertAllAssertions(Goal goal) {
        for (NoPosTacletApp t : replayVisitor.getSmtReplayer().getAllAssertionInsertTaclets()) {
            goal = goal.apply(t).head();
        }
        return goal;
    }

    private Goal insertAllHypotheses(Goal goal) {
        for (Map.Entry<Term, NoPosTacletApp> h : replayVisitor.getHypoTaclets().entrySet()) {
            goal = goal.apply(h.getValue()).head();
        }
        return goal;
    }
}
