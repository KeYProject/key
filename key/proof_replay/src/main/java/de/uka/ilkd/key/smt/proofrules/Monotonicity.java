package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTProofParser;

import java.util.List;

public class Monotonicity extends ProofRule {
    public Monotonicity(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(SMTProofParser.ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = ReplayTools.applyInteractive(goal, app).toList();

        Goal left = goals.get(1);

        // run auto mode directly, implementation below does not work
        ReplayTools.runAutoMode(left);
        assert left.node().isClosed();

        /*
        Node pruneTarget = left.node();
        try {
            // monotonicity currently is very fragile and only partly implemented
            // (hidden reflexive proofs, = vs. <->, problems with typeguard/instanceof,
            // additional unknown reasoning steps in some proofs, ...). Therefore if our manual
            // steps fail (with an Exception), we prune the proof and run auto mode.

            SequentFormula seqForm = left.sequent().antecedent().get(0);
            PosInOccurrence pio;

            int params = 1;

            // TODO: in at least one of my examples, some strange rewriting steps happened

            // andLeft
            while (seqForm.formula().op() == Junctor.AND) {
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = ReplayTools.createTacletApp("andLeft", pio, left);
                left = ReplayTools.applyInteractive(left, app).head();
                seqForm = left.sequent().antecedent().get(0);
                params++;
            }

            // apply equalities
            for (int i = 0; i < params; i++) {

                // TODO: =
                //seqForm = left.sequent().succedent().get(0);
                //pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0).down(i), false);
                //app = ReplayTools.createTacletApp("applyEq", pio, left);
                //left = ReplayTools.applyInteractive(left, app).head();

                // <->
                seqForm = left.sequent().antecedent().get(i);
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = ReplayTools.createTacletApp("insert_eqv_once_lr", pio, left);
                left = ReplayTools.applyInteractive(left, app).head();


                seqForm = left.sequent().succedent().get(0);
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0).down(i), false);
                //app = ReplayTools.createTacletApp("insert_eqv", pio, left);
                // TODO: is there always only one locally introduced rule?
                Iterable<NoPosTacletApp> localRules = left.node().getLocalIntroducedRules();
                app = localRules.iterator().next();
                app = ReplayTools.autoInst(app, pio, left);
                left = ReplayTools.applyInteractive(left, app).head();
            }

            // TODO: =
            //seqForm = left.sequent().succedent().get(0);
            //pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            //app = ReplayTools.createTacletApp("eqClose", pio, left);
            //left = ReplayTools.applyInteractive(left, app).head();

            // <->
            seqForm = left.sequent().succedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            app = ReplayTools.createTacletApp("eq_eq", pio, left);
            left = ReplayTools.applyInteractive(left, app).head();

            seqForm = left.sequent().succedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            app = ReplayTools.createTacletApp("closeTrue", pio, left);
            left = ReplayTools.applyInteractive(left, app).head();
        } catch (Exception e) {
            // we show the exception, but only on cli
            e.printStackTrace();
            System.out.println("Manual monotonicity replay failed, running auto mode ...");
            // revert the replay attempt and try to close automatically
            pruneTarget.proof().pruneProof(pruneTarget);
            left = pruneTarget.proof().getGoal(pruneTarget);
            ReplayTools.runAutoModePropositional(left, 1000);
            assert left.node().isClosed();
        }*/
        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }
}
