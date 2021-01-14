package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.util.Pair;

import java.util.Iterator;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class QuantIntro extends ProofRule {
    public QuantIntro(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        // we expect: quant-intro (lambda ((x S) (y T) ...) phi)
        // sequent: ==> Qx. Qy. ... phi(x,y,...) <-> Qx. Qy. ... psi(x,y,...)

        // cut: forall x. forall y. ... phi(x,y,...) <-> psi(x,y,...)
        // TODO: on the right side there may be an ~ (which is converted to <->), <-> or =
        Term expectedTerm = extractRuleAntecedents(ctx);
        // we do not use the term here for a cut, since we need to introduce fresh skolem symbols,
        // however, we can compare our skolemized term to that extracted from the rule antecedent

        // extract lambda bound var count
        int freeVarCount = extractFreeVarCount(ctx);

        SequentFormula conclusion = goal.sequent().succedent().getFirst();
        /*
        Term t = conclusion.formula();

        assert t.op() == Equality.EQV;

        Term l = t.sub(0);
        Term r = t.sub(1);

        assert l.op() == Quantifier.EX || l.op() == Quantifier.ALL;
        assert r.op() == Quantifier.EX || r.op() == Quantifier.ALL;
        assert l.boundVars().size() == 1;
        assert r.boundVars().size() == 1;

        QuantifiableVariable qvL = l.boundVars().last();
        QuantifiableVariable qvR = r.boundVars().last();
        Term leftUnderQuant = l.sub(0);
        Term rightUnderQuant = r.sub(0);

        // replace to have same quantified variable
        Term rightRepl = ReplayTools.replace(qvR, qvL, rightUnderQuant, services);

        // note that we always create forall!
        TermBuilder tb = services.getTermBuilder();
        TermFactory tf = services.getTermFactory();
        Term cutTerm = tb.all(qvL, tf.createTerm(Equality.EQV, leftUnderQuant, rightRepl));
        */

        Term cutTerm = expectedTerm;
        TacletApp cutApp = ReplayTools.createCutApp(goal, cutTerm);
        //assert cutTerm.equals(expectedTerm); // apart from renaming

        List<Goal> goals = ReplayTools.applyInteractive(goal, cutApp).toList();

        ////////////////////////////////////////////////////////////////////////////////////////////
        // forall x. forall y. ... p(x,y,...) <-> q(x,y,...)
        // ==>
        // Q x. Q y. ... p(x,y,...) <-> Q x. Q y. ... q(x,y,...)
        Goal left = goals.get(1);
        SequentFormula quantEquiv = ReplayTools.getLastAddedAntec(left);

        PosInOccurrence pio = new PosInOccurrence(conclusion, PosInTerm.getTopLevel(), false);
        TacletApp splitEquiv = ReplayTools.createTacletApp("equiv_right", pio, left);
        List<Goal> splitGoals = ReplayTools.applyInteractive(left, splitEquiv).toList();
        // forall x. p(x) <-> q(x), Q x. p(x) ==> Q x. q(x)
        Goal splitLeft = splitGoals.get(0);
        SequentFormula rhs = ReplayTools.getLastAddedSuc(splitLeft);
        if (rhs.formula().op() == Quantifier.ALL) {                                     // forall
            quantIntroAll(quantEquiv, splitGoals, freeVarCount);
        } else {                                                                        // exists
            quantIntroEx(quantEquiv, splitGoals, freeVarCount);
        }
        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);

        // TODO: for uniform treatment of nnf and qintro rules, skolemization should be in bind rule

        // skolemize formula with newly introduced top level forall
        SequentFormula all = ReplayTools.getLastAddedSuc(goal);

        // repeat for every lambda bound variable (terms with additional quantifiers have been
        // created by DefCollector!):
        for (int i = 0; i < freeVarCount; i++) {
            pio = new PosInOccurrence(all, PosInTerm.getTopLevel(), false);
            TacletApp app = ReplayTools.createTacletApp("allRight", pio, goal);
            goal = ReplayTools.applyInteractive(goal, app).head();

            // hide all other formulas
            SequentFormula skolemized = ReplayTools.getLastAddedSuc(goal);
            goal = ReplayTools.focus(skolemized, goal, false);

            // get the new skolem symbol and push it to stack:
            // it must be available when replaying any in this subtree
            SVInstantiations svInsts = app.instantiations();
            Iterator<SchemaVariable> iterator = svInsts.svIterator();
            SchemaVariable skSv = null;
            while (iterator.hasNext()) {
                SchemaVariable sv = iterator.next();
                if (sv instanceof SkolemTermSV) {
                    skSv = sv;
                    break;
                }
            }
            assert skSv != null;
            final Term inst = (Term) svInsts.getInstantiation(skSv);
            final QuantifiableVariable boundVar = all.formula().boundVars().get(0);
            replayVisitor.getSkolemSymbols().push(new Pair<>(boundVar, inst));
            // proceed with next quantifier
            all = skolemized;
        }

        continueReplay(ctx.proofsexpr(0));

        // when returning from this subtree, we forget the instantiations
        for (int i = 0; i < freeVarCount; i++) {
            replayVisitor.getSkolemSymbols().pop();
        }
        return goal;
    }

    private int extractFreeVarCount(ProofsexprContext ctx) {
        ProofsexprContext proofBind =
            (ProofsexprContext) ReplayTools.ensureLookup(ctx.proofsexpr(0), replayVisitor);
        ProofsexprContext lambda =
            (ProofsexprContext) ReplayTools.ensureLookup(proofBind.proofsexpr(0), replayVisitor);
        return lambda.sorted_var().size();
    }

    private void quantIntroAll(SequentFormula quantEquiv, Goal goal, boolean pq, int freeVarCount) {
        // forall x. forall y. ... p(x,y,...) <-> q(x,y,...), forall x. forall y. ... p(x,y,...)
        // ==> forall x. forall y. ... q(x,y,...)

        // note: p and q are swapped if pq flag is set
        SequentFormula rhs = ReplayTools.getLastAddedSuc(goal);
        SequentFormula lhs = ReplayTools.getLastAddedAntec(goal);

        SequentFormula seqForm = quantEquiv;
        for (int i = 0; i < freeVarCount; i++) {
            // allRight
            PosInOccurrence pio = new PosInOccurrence(rhs, PosInTerm.getTopLevel(), false);
            TacletApp app = ReplayTools.createTacletApp("allRight", pio, goal);
            goal = ReplayTools.applyInteractive(goal, app).head();

            rhs = ReplayTools.getLastAddedSuc(goal);

            // get the new skolem constant from the last rule application
            SVInstantiations svInsts = app.instantiations();
            Iterator<SchemaVariable> iterator = svInsts.svIterator();
            SchemaVariable skSv = null;
            while (iterator.hasNext()) {
                SchemaVariable sv = iterator.next();
                if (sv instanceof SkolemTermSV) {
                    skSv = sv;
                    break;
                }
            }
            assert skSv != null;
            Term inst = (Term) svInsts.getInstantiation(skSv);

            // allLeft
            pio = new PosInOccurrence(lhs, PosInTerm.getTopLevel(), true);
            app = ReplayTools.createTacletApp("allLeft", pio, goal);
            SchemaVariable qvSv = app.uninstantiatedVars().iterator().next();
            app = app.addInstantiation(qvSv, inst, true, services);
            goal = ReplayTools.applyInteractive(goal, app).head();

            lhs = ReplayTools.getLastAddedAntec(goal);

            // allLeft
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = ReplayTools.createTacletApp("allLeft", pio, goal);
            qvSv = app.uninstantiatedVars().iterator().next();
            app = app.addInstantiation(qvSv, inst, true, services);
            goal = ReplayTools.applyInteractive(goal, app).head();

            seqForm = ReplayTools.getLastAddedAntec(goal);
        }

        // replace_known_left
        if (pq) {
            PosInTerm pit = PosInTerm.getTopLevel().down(0);
            SequentFormula sf = new SequentFormula(pit.getSubTerm(seqForm.formula()));
            // the top level symbol (<-> or =) may be commutated
            if (goal.sequent().antecedent().containsEqual(sf)) {
                goal = ReplayTools.applyNoSplitPosAntec(goal, "replace_known_left", pit, seqForm);
                // concrete_eq_1
                seqForm = ReplayTools.getLastModifiedAntec(goal);
                goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_eq_1", seqForm);
            } else {
                pit = PosInTerm.getTopLevel().down(1);
                goal = ReplayTools.applyNoSplitPosAntec(goal, "replace_known_left", pit, seqForm);
                // concrete_eq_1
                seqForm = ReplayTools.getLastModifiedAntec(goal);
                goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_eq_3", seqForm);
            }
        } else {
            PosInTerm pit = PosInTerm.getTopLevel().down(1);
            SequentFormula sf = new SequentFormula(pit.getSubTerm(seqForm.formula()));
            // the top level symbol (<-> or =) may be commutated
            if (goal.sequent().antecedent().containsEqual(sf)) {
                goal = ReplayTools.applyNoSplitPosAntec(goal, "replace_known_left", pit, seqForm);
                // concrete_eq_3
                seqForm = ReplayTools.getLastModifiedAntec(goal);
                goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_eq_3", seqForm);
            } else {
                pit = PosInTerm.getTopLevel().down(0);
                goal = ReplayTools.applyNoSplitPosAntec(goal, "replace_known_left", pit, seqForm);
                // concrete_eq_3
                seqForm = ReplayTools.getLastModifiedAntec(goal);
                goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_eq_1", seqForm);
            }
        }

        // closeAntec
        seqForm = ReplayTools.getLastModifiedAntec(goal);
        goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "closeAntec", seqForm);
    }

    private void quantIntroAll(SequentFormula quantEquiv, List<Goal> splitGoals, int freeVarCount) {
        quantIntroAll(quantEquiv, splitGoals.get(0), true, freeVarCount);
        // in the other branch of the split, we do basically the same with swapped p and q (leads to
        // rules name and position changes!)
        quantIntroAll(quantEquiv, splitGoals.get(1), false, freeVarCount);
    }

    private void quantIntroEx(SequentFormula quantEquiv, Goal goal, boolean pq, int freeVarCount) {
        // forall x. forall y. ... p(x,y,...) <-> q(x,y,...), exists x. exists y. ... p(x,y,...)
        // ==> exists x. exists. ... q(x,y,...)

        // note: p and q are swapped if pq flag is set
        SequentFormula rhs = ReplayTools.getLastAddedSuc(goal);
        SequentFormula lhs = ReplayTools.getLastAddedAntec(goal);

        SequentFormula seqForm = quantEquiv;
        for (int i = 0; i < freeVarCount; i++) {
            // exLeft
            PosInOccurrence pio = new PosInOccurrence(lhs, PosInTerm.getTopLevel(), true);
            TacletApp app = ReplayTools.createTacletApp("exLeft", pio, goal);
            goal = ReplayTools.applyInteractive(goal, app).head();

            lhs = ReplayTools.getLastAddedAntec(goal);

            // get the new skolem constant from the last rule application
            SVInstantiations svInsts = app.instantiations();
            Iterator<SchemaVariable> iterator = svInsts.svIterator();
            SchemaVariable skSv = null;
            while (iterator.hasNext()) {
                SchemaVariable sv = iterator.next();
                if (sv instanceof SkolemTermSV) {
                    skSv = sv;
                    break;
                }
            }
            assert skSv != null;
            final Term inst = (Term) svInsts.getInstantiation(skSv);

            // exRight
            pio = new PosInOccurrence(rhs, PosInTerm.getTopLevel(), false);
            app = ReplayTools.createTacletApp("exRight", pio, goal);
            SchemaVariable qvSv = app.uninstantiatedVars().iterator().next();
            app = app.addInstantiation(qvSv, inst, true, services);
            goal = ReplayTools.applyInteractive(goal, app).head();

            rhs = ReplayTools.getLastAddedSuc(goal);

            // allLeft
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = ReplayTools.createTacletApp("allLeft", pio, goal);
            qvSv = app.uninstantiatedVars().iterator().next();
            app = app.addInstantiation(qvSv, inst, true, services);
            goal = ReplayTools.applyInteractive(goal, app).head();

            seqForm = ReplayTools.getLastAddedAntec(goal);
        }

        // replace_known_left
        if (pq) {
            PosInTerm pit = PosInTerm.getTopLevel().down(1);
            goal = ReplayTools.applyNoSplitPosAntec(goal, "replace_known_left", pit, seqForm);

            // concrete_eq_3
            seqForm = ReplayTools.getLastModifiedAntec(goal);
            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_eq_3", seqForm);
        } else {
            PosInTerm pit = PosInTerm.getTopLevel().down(0);
            goal = ReplayTools.applyNoSplitPosAntec(goal, "replace_known_left", pit, seqForm);

            // concrete_eq_1
            seqForm = ReplayTools.getLastModifiedAntec(goal);
            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_eq_1", seqForm);
        }

        // closeAntec
        seqForm = ReplayTools.getLastModifiedAntec(goal);
        goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "closeAntec", seqForm);
    }

    private void quantIntroEx(SequentFormula quantEquiv, List<Goal> splitGoals, int freeVarCount) {
        quantIntroEx(quantEquiv, splitGoals.get(0), true, freeVarCount);
        // in the other branch of the split, we do basically the same with swapped p and q (leads to
        // rules name and position changes!)
        quantIntroEx(quantEquiv, splitGoals.get(1), false, freeVarCount);
    }
}
