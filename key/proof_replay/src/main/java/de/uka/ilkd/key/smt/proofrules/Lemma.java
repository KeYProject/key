package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.*;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import static de.uka.ilkd.key.smt.SMTProofParser.*;
import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class Lemma extends ProofRule {
    public Lemma(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // note: connected to hypothesis rule, see class Hypothesis
        //List<Term> hypotheses = extractHypotheses(ctx);
        SMTReplayer replayer = replayVisitor.getSmtReplayer();
        Set<NoprooftermContext> hypotheses = HypothesisExtractor.extractHypotheses(replayer, ctx);

        assert hypotheses.size() >= 1;

        List<Term> hypothesisTerms = new ArrayList<>();

        TermFactory tf = services.getTermFactory();
        //Term cutTerm = hypotheses.get(0);
        Iterator<NoprooftermContext> it = hypotheses.iterator();

        // TODO: bound vars/skolem symbols?
        Term cutTerm = DefCollector.convertToKeY(replayer, services, it.next());
        hypothesisTerms.add(cutTerm);
        //for (int i = 1; i < hypotheses.size(); i++) {
        while (it.hasNext()) {
            //Term h = hypotheses.get(i);

            // TODO: bound vars/skolem symbols?
            Term h = DefCollector.convertToKeY(replayer, services, it.next());
            hypothesisTerms.add(h);
            h = ReplayTools.ensureFormula(h, services);
            cutTerm = tf.createTerm(Junctor.AND, cutTerm, h);
        }
        // while technically not necessary, the enclosing negation allows us to use rideSideHelper
        cutTerm = ReplayTools.ensureFormula(cutTerm, services);
        cutTerm = tf.createTerm(Junctor.NOT, cutTerm);

        // apply cut
        TacletApp cutApp = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(cutApp).toList();
        Goal left = goals.get(1);

        // todo: really simple steps on the original conlcusion
        // notLeft
        // orRight (n-1 times)
        // notRight (n times)
        // replace_known_left (n times)
        // concrete_and_ (n-1 times)
        // close
        ReplayTools.runAutoMode(left);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        SequentFormula cutFormula = ReplayTools.getLastAddedSuc(goal);

        // notRight
        SequentFormula seqForm = cutFormula;
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "notRight", seqForm);

        // andLeft (n-1 times)
        seqForm = ReplayTools.getLastAddedAntec(goal);
        for (int i = 0; i < hypotheses.size() - 1; i++) {
            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "andLeft", seqForm);
            seqForm = ReplayTools.getLastModifiedSuc(goal);
        }

        /*
        // split and (andRight n-1 times)
        SequentFormula sf = ReplayTools.getLastAddedAntec(goal);
        for (int i = 0; i < hypotheses.size() - 1; i++) {
            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "andRight", sf);
            sf = ReplayTools.getLastModifiedAntec(goal);
        }
        */

        // hide hypotheses and remember the mapping to insert_taclets
        for (Term h : hypothesisTerms) {
            // fix: we need the exact SequentFormula instance!
            //SequentFormula hf = new SequentFormula(h);
            SequentFormula hf = findSequentFormulaForTerm(goal, h, true);
            assert hf != null;

            PosInOccurrence pio = new PosInOccurrence(hf, PosInTerm.getTopLevel(), true);
            TacletApp hide = ReplayTools.createTacletApp("hide_left", pio, goal);
            goal = goal.apply(hide).head();
            NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();
            replayVisitor.getHypoTaclets().put(h, insertRule);
        }

        // no we have the hypotheses available as taclets and descend further

        // note: we can not use this, since hide taclets have no lastAdded/Modified formula
        //replayRightSideHelper(ctx);
        replayRightSideHelper(ctx, cutFormula);

        // since we leave this subtree now, hypotheses are no longer available
        for (Term h : hypothesisTerms) {
            replayVisitor.getHypoTaclets().remove(h);
        }
        return goal;
    }

    // Note: it is not sufficient to look only at the at the lemma rule only:
    //  One can not decide if a term (!l1 | ... | !ln) are n hypotheses or a single one.
    //  Therefore, HypothesisExtractor visitor should be used, which walks the proof tree and
    //  the used hypotheses directly from "hypothesis" rules.
    // helper method for replayLemma()
    private List<Term> extractHypotheses(ProofsexprContext ctx) {
        // format: (or !h0 !h1 ... !hn)
        List<Term> hypotheses = new ArrayList<>();
        NoprooftermContext conclCtx = extractRuleConclusionCtx(ctx).noproofterm();

        Term rest = extractRuleConclusion(ctx);

        int hypoCount = 0;
        if (conclCtx.func != null && conclCtx.func.getText().equals("or")) {
            hypoCount = conclCtx.noproofterm().size() - 1;  // "or" + params

            for (int i = 0; i < hypoCount; i++) {
                Term h = rest.sub(i);
                assert h.op() == Junctor.NOT;
                hypotheses.add(h.sub(0));

                /*
                Term notH = rest.sub(1);
                // TODO: negation necessary if positive?
                assert notH.op() == Junctor.NOT;
                Term h = notH.sub(0);
                hypotheses.add(h);
                rest = rest.sub(0);
                 */
            }
        } else {
            hypoCount = 1;
            assert rest.op() == Junctor.NOT;
            // TODO: negate if positive!
            hypotheses.add(rest.sub(0));
        }
        return hypotheses;
    }
}
