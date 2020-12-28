package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.smt.SMTProofParser.IdentifierContext;
import de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;
import de.uka.ilkd.key.smt.proofrules.*;
import de.uka.ilkd.key.util.Pair;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.*;

/**
 * This class is responsible for the actual replay of rules. For every rule there is a separate
 * method. Replay of a rule is started when visiting the corresponding parser context.
 *
 * @author Wolfram Pfeifer
 */
public class ReplayVisitor extends SMTProofBaseVisitor<Void> {
    /** the replayer object (for looking up symbols) */
    private final SMTReplayer smtReplayer;

    /** the goal the visitor is currently working on (changed by the replay methods!) */
    private Goal goal;

    /** services used for building terms and looking up symbols */
    private final Services services;

    /** Taclets for inserting hypotheses discharged by previously replayed lemma rules. The
     * hypotheses are hidden in insert taclets (and can be re-introduced if needed) because the
     * focus rule is applied for every rule, which would hide the hypotheses as well. */
    //private final Map<Term, NoPosTacletApp> hypoTaclets = new HashMap<>();
    private final Map<Term, NoPosTacletApp> hypoTaclets = new TreeMap<>((o1, o2) -> {
        // bound variables may be renamed!
        if (o1.equalsModRenaming(o2)) {
            return 0;
        }
        // default to String comparison (since we need a welldefined order)
        return o1.toString().compareTo(o2.toString());
    });

    /** used to carry symbols introduced by quant-intro rule (needed for replaying rules inside
     * the scope of a quant-intro/proof-bind/lambda) */
    private final Deque<Pair<QuantifiableVariable, Term>> skolemSymbols = new LinkedList<>();

    public ReplayVisitor(SMTReplayer smtReplayer, Goal goal) {
        this.smtReplayer = smtReplayer;
        this.goal = goal;
        this.services = goal.proof().getServices();
    }

    @Override
    public Void visitProofsexpr(ProofsexprContext ctx) {

        // do not descend into let terms
        if (ctx.LET() != null) {
            return null;
        }

        Token rule = ctx.rulename;
        if (rule == null) {
            return super.visitProofsexpr(ctx);
        }

        // add (inlined) context to node in proof tree
        TextCollector tc = new TextCollector(smtReplayer, ctx);
        tc.visit(ctx);
        String unsharedText = tc.getResult();
        ReplayTools.addNotes(goal, unsharedText);

        String rulename = ctx.rulename.getText();
        switch (rulename) {
        case "true-axiom":
            goal = new True(services, goal, this).replay(ctx);
            return null;
        case "goal":            // goal is semantically equal to asserted
        case "asserted":
            goal = new Asserted(services, goal, this).replay(ctx);
            return null;
        case "rewrite":
            goal = new Rewrite(services, goal, this).replay(ctx);
            return null;
        case "rewrite*":
            goal = new RewriteStar(services, goal, this).replay(ctx);
            return null;
        case "monotonicity":
            goal = new Monotonicity(services, goal, this).replay(ctx);
            return null;
        case "trans":
            goal = new Transitivity(services, goal, this).replay(ctx);
            return null;
        case "trans*":
            goal = new TransitivityStar(services, goal, this).replay(ctx);
            return null;
        case "iff-true":
            goal = new IffTrue(services, goal, this).replay(ctx);
            return null;
        case "iff-false":
            goal = new IffFalse(services, goal, this).replay(ctx);
            return null;
        case "commutativity":
            goal = new Commutativity(services, goal, this).replay(ctx);
            return null;
        case "not-or-elim":
            goal = new NotOrElim(services, goal, this).replay(ctx);
            return null;
        case "and-elim":
            goal = new AndElim(services, goal, this).replay(ctx);
            return null;
        case "mp":      // since we replace ~ by <-> and eps, mp and mp~ can be treated the same
        case "mp~":
            goal = new ModusPonens(services, goal, this).replay(ctx);
            return null;
        case "unit-resolution":
            goal = new UnitResolution(services, goal, this).replay(ctx);
            return null;
        case "th-lemma":
            goal = new ThLemma(services, goal, this).replay(ctx);
            return null;
        case "sk":
            goal = new Skolemize(services, goal, this).replay(ctx);
            return null;
        case "quant-intro":
            goal = new QuantIntro(services, goal, this).replay(ctx);
            return null;
        case "symm":
            goal = new Symmetry(services, goal, this).replay(ctx);
            return null;
        case "refl":
            goal = new Reflexivity(services, goal, this).replay(ctx);
            return null;
        case "proof-bind":
            goal = new ProofBind(services, goal, this).replay(ctx);
            return null;
        case "distributivity":
            goal = new Distributivity(services, goal, this).replay(ctx);
            return null;
        case "def-axiom":
            goal = new DefAxiom(services, goal, this).replay(ctx);
            return null;
        case "iff~":
            goal = new IffEquisat(services, goal, this).replay(ctx);
            return null;
        case "quant-inst":
            goal = new QuantInst(services, goal, this).replay(ctx);
            return null;
        case "hypothesis":
            goal = new Hypothesis(services, goal, this).replay(ctx);
            return null;
        case "lemma":
            goal = new Lemma(services, goal, this).replay(ctx);
            return null;
        case "nnf-pos":
            goal = new NNFPos(services, goal, this).replay(ctx);
            return null;
        case "nnf-neg":
            goal = new NNFNeg(services, goal, this).replay(ctx);
            return null;
        case "elim-unused":
            goal = new ElimUnused(services, goal, this).replay(ctx);
            return null;
        default:
            //System.out.println("Replay for rule not yet implemented: " + rulename);
            throw new IllegalStateException("Replay for rule not yet implemented: " + rulename);
            //return null;
        }
        // TODO: factor out method call:
        //ProofRule p;
        //goal = p.replay(ctx);
        //return null;

        //return super.visitProofsexpr(ctx);
    }

    public void visitAtGoal(ParserRuleContext ctx, Goal goal) {
        this.goal = goal;
        visit(ctx);
    }

    @Override
    public Void visit(ParseTree tree) {
        return tree.accept(this);
    }

    @Override
    public Void visitIdentifier(IdentifierContext ctx) {
        ParserRuleContext def = smtReplayer.getSymbolDef(ctx.getText(), ctx);
        if (def != null) {
            // continue proof replay with the partial tree from the symbol table
            visit(def);
        }
        return null;
    }

    /*
    private PosInTerm findFirstSubtermPos(Term t, Term subterm, PosInTerm prefix) {
        if (t.equals(subterm)) {
            return prefix;
        }
        for (int i = 0; i < t.subs().size(); i++) {
            Term child = t.sub(i);
            PosInTerm potentialPrefix = prefix.down(i);
            PosInTerm posInChild = findFirstSubtermPos(child, subterm, potentialPrefix);
            if (posInChild != null) {
                return posInChild;
            }
        }
        return null;
    }

    private PosInTerm findFirstSubtermPos(Term t, Term subterm) {
        return findFirstSubtermPos(t, subterm, PosInTerm.getTopLevel());
    }

    private boolean sameStructureTerms(Term t1, Term t2) {
        if (t1.subs().size() == t2.subs().size()) {
            if (t1.subs().size() == 0) {
                // variables/constants are considered structurally equal
                return true;
            } else {
                if (!t1.op().equals(t2.op())) {
                    // different operators
                    return false;
                }
                for (int i = 0; i < t1.subs().size(); i++) {
                    if (!sameStructureTerms(t1.sub(i), t2.sub(i))) {
                        // at least these two children are different
                        return false;
                    }
                }
                // all children have same structure -> parents have same structure
                return true;
            }
        } else {
            // shortcut: different arities -> different structures
            return false;
        }
    }*/

    public SMTReplayer getSmtReplayer() {
        return smtReplayer;
    }

    public Deque<Pair<QuantifiableVariable, Term>> getSkolemSymbols() {
        return skolemSymbols;
    }

    public Map<Term, NoPosTacletApp> getHypoTaclets() {
        return hypoTaclets;
    }
}
