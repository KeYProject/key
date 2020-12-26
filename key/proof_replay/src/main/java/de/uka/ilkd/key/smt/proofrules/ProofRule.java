package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.DefCollector;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTReplayer;
import de.uka.ilkd.key.util.Pair;
import org.antlr.v4.runtime.ParserRuleContext;

import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public abstract class ProofRule {
    protected final Services services;
    protected final ReplayVisitor replayVisitor;
    protected Goal goal;

    public ProofRule(Services services, Goal goal, ReplayVisitor replayVisitor) {
        this.services = services;       // TODO: services can be extracted from goal or visitor
        this.goal = goal;
        this.replayVisitor = replayVisitor;
    }

    public abstract Goal replay(ProofsexprContext ctx);

    protected Term extractRuleAntecedents(ProofsexprContext ctx) {
        List<ProofsexprContext> children = ctx.proofsexpr();
        if (children.size() == 1) {
            // closing rule (e.g. rewrite, asserted, ...)
            return null;
        } else {
            List<Term> antecs = new ArrayList<>();
            // antecendent of the rule are all terms expect the last one
            for (int i = 0; i < children.size() - 1; i++) {
                ProofsexprContext child = children.get(i);
                antecs.add(lookupOrCreate(child));
            }
            if (antecs.size() == 1) {
                return antecs.get(0);
            }
            Term result = antecs.get(0);
            for (int i = 1; i < antecs.size(); i++) {
                result = ReplayTools.ensureFormula(result, services);
                Term anteFormula = ReplayTools.ensureFormula(antecs.get(i), services);
                result = services.getTermFactory().createTerm(Junctor.AND, result, anteFormula);
            }
            return result;
        }
    }

    /**
     * Splits the formula at the right side of a cut into the different antecedents of a rule and
     * starts replay of the corresponding subtrees.
     *
     * @param ctx
     */
    protected void replayRightSideHelper(ProofsexprContext ctx, SequentFormula cutFormula) {

        goal = ReplayTools.focus(cutFormula, goal, false);

        PosInOccurrence pio;
        TacletApp app;

        // last is succedent, others are subterms
        int antecCount = ctx.proofsexpr().size() - 1;

        for (int i = antecCount - 1; i > 0; i--) {
            pio = new PosInOccurrence(cutFormula, PosInTerm.getTopLevel(), false);
            app = ReplayTools.createTacletApp("andRight", pio, goal);
            List<Goal> antecs = goal.apply(app).toList();

            goal = antecs.get(0);
            continueReplay(ctx.proofsexpr(i));

            goal = antecs.get(1);
            cutFormula = ReplayTools.getLastAddedSuc(goal);
        }
        continueReplay(ctx.proofsexpr(0));
    }

    protected void continueReplay(ParserRuleContext ctx) {
        replayVisitor.visitAtGoal(ctx, goal);
    }

    protected void replayRightSideHelper(ProofsexprContext ctx) {
        SequentFormula cutFormula = ReplayTools.getLastAddedSuc(goal);
        if (cutFormula == null) {
            cutFormula = ReplayTools.getLastModifiedSuc(goal);
        }
        replayRightSideHelper(ctx, cutFormula);
    }

    protected Term lookupOrCreate(ProofsexprContext ctx) {
        // ctx could be:
        // - symbol from KeY (is in translation map)
        // - symbol bound via let
        // - a term with nested rule applications (descend into succedent of the rule)

        SMTReplayer smtReplayer = replayVisitor.getSmtReplayer();
        Deque<Pair<QuantifiableVariable, Term>> skolemSymbols = replayVisitor.getSkolemSymbols();

        Term term = smtReplayer.getTranslationToTerm(ctx.getText());
        if (term == null) {
            // recursively descend into let definition
            ParserRuleContext letDef = smtReplayer.getSymbolDef(ctx.getText(), ctx);
            DefCollector defCollector = new DefCollector(smtReplayer, services, skolemSymbols);
            if (letDef != null) {
                term = letDef.accept(defCollector);
            } else {
                // could be a term containing nested rule applications again
                term = ctx.accept(defCollector);
            }
        }

        // TODO: not sure if this is still needed
        // if we are within the scope of a lambda (i.e. skolemSymbols is not empty),
        // we replace the Z3 variable by our skolem constant
        if (!skolemSymbols.isEmpty()) {
            Pair<QuantifiableVariable, Term> skolemPair = skolemSymbols.peek();
            Term varTerm = services.getTermBuilder().var(skolemPair.first);
            TermFactory tf = services.getTermFactory();
            term = OpReplacer.replace(varTerm, skolemPair.second, term, tf);
        }

        return term;
    }

    protected ProofsexprContext extractRuleConclusionCtx(ProofsexprContext ctx) {
        return ctx.proofsexpr(ctx.proofsexpr().size() - 1);
    }

    protected Term extractRuleConclusion(ProofsexprContext ctx) {
        ProofsexprContext conclusionCtx = extractRuleConclusionCtx(ctx);
        return lookupOrCreate(conclusionCtx);
    }

    // this method is necessary, since some checks in apply work with == instead of equals and thus
    // we need the exact SequentFormula instance when applying taclets
    protected static SequentFormula findSequentFormulaForTerm(Goal goal, Term term, boolean inAntec) {
        Semisequent semi;
        if (inAntec) {
            semi = goal.sequent().antecedent();
        } else {
            semi = goal.sequent().succedent();
        }
        // we search for a SF that is equal to this one
        SequentFormula searchedSF = new SequentFormula(term);
        for (SequentFormula current : semi.asList()) {
            // TODO: for some strange reason, even if the formulas are equal when written to String,
            //  their equal method may sometimes return false ...
            if (current.toString().equals(searchedSF.toString())) {
            //if (current.equals(searchedSF)) {
                return current;
            }
        }
        return null;
    }

    // this method is necessary, since some checks in apply work with == instead of equals and thus
    // we need the exact SequentFormula instance when applying taclets
    protected static SequentFormula findSequentFormulaForTerm(Goal goal, Term term) {
        // we search for a SF that is equal to this one
        SequentFormula searchedSF = new SequentFormula(term);
        for (SequentFormula current : goal.sequent().asList()) {
            if (current.equals(searchedSF)) {
                return current;
            }
        }
        return null;
    }
}
