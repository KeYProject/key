package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.smt.SMTProofParser.IdentifierContext;
import de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;
import de.uka.ilkd.key.util.Pair;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.util.*;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

/**
 * This class is responsible for the actual replay of rules. For every rule there is a separate
 * method. Replay of a rule is started when visiting the corresponding parser context.
 *
 * @author Wolfram Pfeifer
 */
class ReplayVisitor extends SMTProofBaseVisitor<Void> {
    /** the replayer object (for looking up symbols) */
    private final SMTReplayer smtReplayer;

    /** the goal the visitor is currently working on (changed by the replay methods!) */
    private Goal goal;

    /** services used for building terms and looking up symbols */
    private final Services services;

    /** Taclets for inserting hypotheses discharged by previously replayed lemma rules. The
     * hypotheses are hidden in insert taclets (and can be re-introduced if needed) because the
     * focus rule is applied for every rule, which would hide the hypotheses as well. */
    private final Map<Term, NoPosTacletApp> hypoTaclets = new HashMap<>();

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

        String rulename = ctx.rulename.getText();
        //System.out.println(rulename);
        System.out.println(ReplayTools.getOriginalText(ctx));
        ReplayTools.addNotes(goal, ReplayTools.getOriginalText(ctx));

        switch (rulename) {
        case "true-axiom":
            replayTrue(ctx);
            return null;
        case "goal":            // goal is semantically equal to asserted
        case "asserted":
            replayAsserted(ctx);
            return null;
        case "rewrite":
            replayRewrite(ctx);
            return null;
        case "rewrite*":
            replayRewriteStar(ctx);
            return null;
        case "monotonicity":
            replayMonotonicity(ctx);
            return null;
        case "trans":
            replayTrans(ctx);
            return null;
        case "trans*":
            replayTransStar(ctx);
            return null;
        case "iff-true":
            replayIffTrue(ctx);
            return null;
        case "iff-false":
            replayIffFalse(ctx);
            return null;
        case "commutativity":
            replayCommutativity(ctx);
            return null;
        case "not-or-elim":
            replayNotOrElim(ctx);
            return null;
        case "and-elim":
            replayAndElim(ctx);
            return null;
        case "mp":      // since we replace ~ by <-> and eps, mp and mp~ can be treated the same
        case "mp~":
            replayMp(ctx);
            return null;
        case "unit-resolution":
            replayUnitResolution(ctx);
            return null;
        case "th-lemma":
            replayThLemma(ctx);
            return null;
        case "sk":
            replaySk(ctx);
            return null;
        case "quant-intro":
            replayQuantIntro(ctx);
            return null;
        case "symm":
            replaySymm(ctx);
            return null;
        case "refl":
            replayRefl(ctx);
            return null;
        case "proof-bind":
            replayProofBind(ctx);
            return null;
        case "distributivity":
            replayDistributivity(ctx);
            return null;
        case "def-axiom":
            replayDefAxiom(ctx);
            return null;
        case "iff~":
            replayIffEquisat(ctx);
            return null;
        case "quant-inst":
            replayQuantInst(ctx);
            return null;
        case "hypothesis":
            replayHypothesis(ctx);
            return null;
        case "lemma":
            replayLemma(ctx);
            return null;
        case "nnf-pos":
            replayNNFPos(ctx);
            return null;
        case "nnf-neg":
            replayNNFNeg(ctx);
            return null;
        default:
            System.out.println("Replay for rule not yet implemented: " + rulename);
            //throw new IllegalStateException("Replay for rule not yet implemented: " + rulename);
            return null;
        }
        //return super.visitProofsexpr(ctx);
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

    ////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////// non-closing rules ///////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////

    private void replayNNFPos(ProofsexprContext ctx) {
        Term antecedent = extractRuleAntecedents(ctx);
        TacletApp cutApp = ReplayTools.createCutApp(goal, antecedent);
        List<Goal> goals = goal.apply(cutApp).toList();
        Goal left = goals.get(1);

        // currently we run auto mode for converting to nnf
        ReplayTools.runAutoMode(left);
        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayNNFNeg(ProofsexprContext ctx) {
        Term antecedent = extractRuleAntecedents(ctx);
        TacletApp cutApp = ReplayTools.createCutApp(goal, antecedent);
        List<Goal> goals = goal.apply(cutApp).toList();
        Goal left = goals.get(1);

        // currently we run auto mode for converting to nnf
        ReplayTools.runAutoMode(left);
        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayCommutativity(ProofsexprContext ctx) {
        // to be safe here: cut with antecendent and run auto mode, since we do not know which
        // operator is used
        Term cutTerm = extractRuleAntecedents(ctx);

        TacletApp cutApp = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(cutApp).toList();
        Goal left = goals.get(1);

        ReplayTools.runAutoModePropositional(left, 50);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayDistributivity(ProofsexprContext ctx) {
        // TODO: restrict to specific rules? better "manual" replay?
        ReplayTools.runAutoModePropositional(goal, 50);
    }

    // this rule should not be used except with CONTEXT_SIMPLIFIER=true or BIT2BOOL=true
    private void replayRewriteStar(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);

        // close this goal by auto mode
        ReplayTools.runAutoModePropositional(left, 50);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayDefAxiom(ProofsexprContext ctx) {
        // closing rule (Tseitin axioms)
        // quick and dirty solution: use auto mode (simple propositional steps)
        // TODO: implement schemas
        ReplayTools.runAutoModePropositional(goal, 50);
    }

    private void replayProofBind(ProofsexprContext ctx) {
        ParserRuleContext lambdaPRC = ensureLookup(ctx.proofsexpr(0));
        if (!(lambdaPRC instanceof ProofsexprContext)) {
            throw new IllegalStateException("Error! After 'proof-bind', 'lambda' is expected!");
        }
        ProofsexprContext lambda = (ProofsexprContext) lambdaPRC;
        if (lambda.rulename == null
            || !lambda.rulename.getText().equals("lambda")) {
            throw new IllegalStateException("Error! After 'proof-bind', 'lambda' is expected!");
        }

        // lambda could still be a symbol bound by let
        ParserRuleContext letDef = smtReplayer.getSymbolDef(lambda.getText(), lambda);
        if (letDef != null) {
            // lambda is var name, letDef is: (lambda ...)
            // TODO: check instanceof
            ProofsexprContext lambdaScope = ((ProofsexprContext)letDef).proofsexpr(0);
            skipLetBindings(lambdaScope);
        } else {
            // lambda is term: (lambda ...)
            ProofsexprContext lambdaScope = lambda.proofsexpr(0);
            skipLetBindings(lambdaScope);
        }
    }

    private void skipLetBindings(ProofsexprContext ctx) {
        if (ctx.LET() != null) {
            // skipped a single let now, there may be more ...
            skipLetBindings(ctx.proofsexpr(0));
        } else {
            visit(ctx);
        }
    }

    // assumption: sequent only single formula in succedent (antecedent should be empty)
    // sequent: ==> A = A     or     ==> A <-> A

    private void replayRefl(ProofsexprContext ctx) {
        SequentFormula seqForm = goal.sequent().succedent().getFirst();
        if (seqForm.formula().op() == Equality.EQUALS) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "eqClose", seqForm);
        } else if (seqForm.formula().op() == Equality.EQV) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "eq_eq", seqForm);
        } else {
            throw new IllegalStateException("Top level operator should be = or <-> but is "
                + seqForm.formula().op());
        }
        seqForm = ReplayTools.getLastModifiedSuc(goal);
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "closeTrue", seqForm);
        // goal is closed now!
    }
    // assumption: sequent only single formula in succedent (antecedent should be empty)
    // sequent: ==> A = B

    private void replaySymm(ProofsexprContext ctx) {
        // TODO: we do not check that the premise of the rule is really the symmetric formula
        SequentFormula seqForm = goal.sequent().succedent().getFirst();
        Operator op = seqForm.formula().op();
        if (op == Equality.EQUALS) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "eqSymm", seqForm);
        } else if (op == Equality.EQV) {
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "equivSymm", seqForm);
        } else {
            throw new IllegalStateException("Operator not known to be symmetric: " + op);
        }
        replayRightSideHelper(ctx);
    }

    private void quantIntroAll(SequentFormula quantEquiv, Goal goal, boolean pq) {
        // forall x. p(x) <-> q(x), forall x. p(x) ==> forall x. q(x)
        // note: p and q are swapped if pq flag is set
        SequentFormula rhs = ReplayTools.getLastAddedSuc(goal);
        SequentFormula lhs = ReplayTools.getLastAddedAntec(goal);

        // allRight
        PosInOccurrence pio = new PosInOccurrence(rhs, PosInTerm.getTopLevel(), false);
        TacletApp app = ReplayTools.createTacletApp("allRight", pio, goal);
        goal = goal.apply(app).head();

        // get the new skolem constant from the last rule application
        SVInstantiations svInsts = app.instantiations();
        Iterator<SchemaVariable> iterator = svInsts.svIterator();
        SchemaVariable skSv = null;
        while (iterator.hasNext()) {
            SchemaVariable sv = iterator.next();
            if (sv instanceof SkolemTermSV) {
                skSv = sv;
                break;      // TODO: only works with single skolemSV
            }
        }
        assert skSv != null;
        Term inst = (Term) svInsts.getInstantiation(skSv);

        // allLeft
        pio = new PosInOccurrence(lhs, PosInTerm.getTopLevel(), true);
        app = ReplayTools.createTacletApp("allLeft", pio, goal);
        SchemaVariable qvSv = app.uninstantiatedVars().iterator().next();
        app = app.addInstantiation(qvSv, inst, true, services);
        goal = goal.apply(app).head();

        // allLeft
        pio = new PosInOccurrence(quantEquiv, PosInTerm.getTopLevel(), true);
        app = ReplayTools.createTacletApp("allLeft", pio, goal);
        qvSv = app.uninstantiatedVars().iterator().next();
        app = app.addInstantiation(qvSv, inst, true, services);
        goal = goal.apply(app).head();

        // replace_known_left
        SequentFormula seqForm = ReplayTools.getLastAddedAntec(goal);
        if (pq) {
            PosInTerm pit = PosInTerm.getTopLevel().down(0);
            goal =
                ReplayTools.applyNoSplitPosAntec(goal, "replace_known_left", pit, seqForm);
            // concrete_eq_1
            seqForm = ReplayTools.getLastModifiedAntec(goal);
            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_eq_1", seqForm);
        } else {
            PosInTerm pit = PosInTerm.getTopLevel().down(1);
            goal =
                ReplayTools.applyNoSplitPosAntec(goal, "replace_known_left", pit, seqForm);
            // concrete_eq_3
            seqForm = ReplayTools.getLastModifiedAntec(goal);
            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "concrete_eq_3", seqForm);
        }

        // closeAntec
        seqForm = ReplayTools.getLastModifiedAntec(goal);
        goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "closeAntec", seqForm);
    }

    private void quantIntroAll(SequentFormula quantEquiv, List<Goal> splitGoals) {
        quantIntroAll(quantEquiv, splitGoals.get(0), true);
        // in the other branch of the split, we do basically the same with swapped p and q (leads to
        // rules name and position changes!)
        quantIntroAll(quantEquiv, splitGoals.get(1), false);
    }

    private void quantIntroEx(SequentFormula quantEquiv, Goal goal, boolean pq) {
        // forall x. p(x) <-> q(x), exists x. p(x) ==> exists x. q(x)
        // exLeft
        SequentFormula rhs = ReplayTools.getLastAddedSuc(goal);
        SequentFormula seqForm = ReplayTools.getLastAddedAntec(goal);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        TacletApp app = ReplayTools.createTacletApp("exLeft", pio, goal);
        goal = goal.apply(app).head();

        // get the new skolem constant from the last rule application
        SVInstantiations svInsts = app.instantiations();
        Iterator<SchemaVariable> iterator = svInsts.svIterator();
        SchemaVariable skSv = null;
        while (iterator.hasNext()) {
            SchemaVariable sv = iterator.next();
            if (sv instanceof SkolemTermSV) {
                skSv = sv;
                break;      // TODO: only works with single skolemSV
            }
        }
        assert skSv != null;
        final Term inst = (Term) svInsts.getInstantiation(skSv);

        // exRight
        pio = new PosInOccurrence(rhs, PosInTerm.getTopLevel(), false);
        app = ReplayTools.createTacletApp("exRight", pio, goal);
        SchemaVariable qvSv = app.uninstantiatedVars().iterator().next();
        app = app.addInstantiation(qvSv, inst, true, services);
        goal = goal.apply(app).head();

        // allLeft
        pio = new PosInOccurrence(quantEquiv, PosInTerm.getTopLevel(), true);
        app = ReplayTools.createTacletApp("allLeft", pio, goal);
        qvSv = app.uninstantiatedVars().iterator().next();
        app = app.addInstantiation(qvSv, inst, true, services);
        goal = goal.apply(app).head();

        // replace_known_left
        seqForm = ReplayTools.getLastAddedAntec(goal);
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

    private void quantIntroEx(SequentFormula quantEquiv, List<Goal> splitGoals) {
        quantIntroEx(quantEquiv, splitGoals.get(0), true);
        // in the other branch of the split, we do basically the same with swapped p and q (leads to
        // rules name and position changes!)
        quantIntroEx(quantEquiv, splitGoals.get(1), false);
    }

    // sequent: ==> Qx. phi(x) <-> Qx. psi(x)
    private void replayQuantIntro(ProofsexprContext ctx) {
        // cut: forall x. phi(x) <-> psi(x)
        // TODO: on the right side there may be an ~ (which is converted to <->), <-> or =
        Term expectedTerm = extractRuleAntecedents(ctx);
        // we do not use the term here for a cut, since we need to introduce fresh skolem symbols,
        // however, we can compare our skolemized term to that extracted from the rule antecedent

        // TODO: we expect: quant-intro (lambda ((x S)(y T)...) phi)

        SequentFormula conclusion = goal.sequent().succedent().getFirst();
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
        TacletApp cutApp = ReplayTools.createCutApp(goal, cutTerm);
        //assert cutTerm.equals(expectedTerm); // apart from renaming

        List<Goal> goals = goal.apply(cutApp).toList();

        // forall x. p(x) <-> q(x) ==> Q x. p(x) <-> Q x. q(x)
        Goal left = goals.get(1);
        SequentFormula quantEquiv = ReplayTools.getLastAddedAntec(left);

        PosInOccurrence pio = new PosInOccurrence(conclusion, PosInTerm.getTopLevel(), false);
        TacletApp splitEquiv = ReplayTools.createTacletApp("equiv_right", pio, left);
        List<Goal> splitGoals = left.apply(splitEquiv).toList();
        // forall x. p(x) <-> q(x), Q x. p(x) ==> Q x. q(x)
        Goal splitLeft = splitGoals.get(0);
        SequentFormula rhs = ReplayTools.getLastAddedSuc(splitLeft);
        if (rhs.formula().op() == Quantifier.ALL) {                                     // forall
            quantIntroAll(quantEquiv, splitGoals);
        } else {                                                                        // exists
            quantIntroEx(quantEquiv, splitGoals);
        }
        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);

        // skolemize formula with newly introduced top level forall
        SequentFormula all = ReplayTools.getLastAddedSuc(goal);
        pio = new PosInOccurrence(all, PosInTerm.getTopLevel(), false);
        TacletApp app = ReplayTools.createTacletApp("allRight", pio, goal);
        goal = goal.apply(app).head();

        // get the new skolem symbol and push it to stack:
        // it must be available when replaying any in this subtree
        SVInstantiations svInsts = app.instantiations();
        Iterator<SchemaVariable> iterator = svInsts.svIterator();
        SchemaVariable skSv = null;
        while (iterator.hasNext()) {
            SchemaVariable sv = iterator.next();
            if (sv instanceof SkolemTermSV) {
                skSv = sv;
                break;      // TODO: only works with single skolemSV
            }
        }
        assert skSv != null;
        final Term inst = (Term) svInsts.getInstantiation(skSv);
        final QuantifiableVariable boundVar = all.formula().boundVars().get(0);
        skolemSymbols.push(new Pair<>(boundVar, inst));

        visit(ctx.proofsexpr(0));

        // when returning from this subtree, we forget the instantiation
        skolemSymbols.pop();
    }

    private List<PosInTerm> collectQvPositions(Term quant) {
        QuantifiableVariable qv = quant.boundVars().last(); // TODO: there has to be exactly one!
        return collectQvPositionsRec(qv, quant.sub(0), PosInTerm.getTopLevel());
    }
    private List<PosInTerm> collectQvPositionsRec(QuantifiableVariable qv,
                                                  Term subTerm, PosInTerm prefix) {
        List<PosInTerm> result = new ArrayList<>();
        if (subTerm.op() instanceof QuantifiableVariable
            && ReplayTools.equalsOp((QuantifiableVariable) subTerm.op(), qv)) {
            result.add(prefix);
        } else {
            for (int i = 0; i < subTerm.subs().size(); i++) {
                // TODO: fix: we must not descend if there is a binder binding a variable with the
                //  same name and sort (this variable is shadowing qv)
                Term sub = subTerm.sub(i);
                if (sub.op().equals(IfExThenElse.IF_EX_THEN_ELSE)) {
                    System.out.println();
                    //continue;
                } else if (sub.op() instanceof Quantifier) {
                    System.out.println();
                    //continue;
                }
                List<PosInTerm> subPos = collectQvPositionsRec(qv, subTerm.sub(i), prefix.down(i));
                result.addAll(subPos);
            }
        }
        return result;
    }

    private void replayRewrite(ProofsexprContext ctx) {
        if (goal.sequent().succedent().get(0).formula().op() == Equality.EQV) {
            // equiv_right top level to guide the prover
            SequentFormula seqForm = goal.sequent().succedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            TacletApp app = ReplayTools.createTacletApp("equiv_right", pio, goal);
            List<Goal> goals = goal.apply(app).toList();
            // running automode separately on both goals increases success rate
            ReplayTools.runAutoMode(goals.get(0));
            ReplayTools.runAutoMode(goals.get(1));
        } else {
            ReplayTools.runAutoMode(goal);
        }
    }

    private void replayIffTrue(ProofsexprContext ctx) {
        SequentFormula seqForm = goal.sequent().succedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp concreteEq3 = ReplayTools.createTacletApp("concrete_eq_3", pio, goal);
        goal = goal.apply(concreteEq3).head();
        visit(ctx.proofsexpr(0));
    }

    private void replayIffFalse(ProofsexprContext ctx) {
        SequentFormula seqForm = goal.sequent().succedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp concreteEq4 = ReplayTools.createTacletApp("concrete_eq_4", pio, goal);
        goal = goal.apply(concreteEq4).head();
        visit(ctx.proofsexpr(0));
    }

    private void replayAndElim(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);
        SequentFormula orig = left.sequent().succedent().get(0);

        SequentFormula seqForm = left.sequent().antecedent().get(0);
        PosInOccurrence pio;

        // TODO: this line should be wrong!!!
        //  should be ctx.proofsexpr(0).size(), however, this does not resolve symbols bound by let
        int arity = ctx.proofsexpr().size();

        // special case for typeguard

        // this selects the text "typeguard" in the contraposition example
        //smtReplayer.getSymbolDef(ctx.proofsexpr(0).proofsexpr(ctx.proofsexpr(0).proofsexpr().size()-1).getText()).noproofterm().noproofterm(1).noproofterm(0).getText()

        for (int i = 0; i < arity; i++) {
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);

            // should not happen any more, since typeguard is now translated to instanceof
            /*
            if (!pio.subTerm().op().equals(Junctor.AND)) {
                // this may occur if a typeguard has been skipped by the translation
                break;
            }
             */

            app = ReplayTools.createTacletApp("andLeft", pio, left);
            left = left.apply(app).head();
            SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
            // TODO: is the order of the added formulas deterministic?
            seqForm = sci.addedFormulas().tail().head();
            if (seqForm == null) {
                // attention: the formula may be equal to the original one by chance
                break;
            }
        }

        seqForm = left.sequent().succedent().get(0);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        app = ReplayTools.createTacletApp("close", pio, left);
        left = left.apply(app).head();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }



    // notLeft, orRight ..., notRight, ..., closeAntec
    private void replayNotOrElim(ProofsexprContext ctx) {
        final Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);
        final SequentFormula rhs = left.sequent().succedent().get(0);
        SequentFormula seqForm = ReplayTools.getLastAddedAntec(left);

        // to avoid cases where a temporary formula is equal to the conclusion
        // (and thus destroying all index calculations), we hide the original rhs here
        left = ReplayTools.applyNoSplitTopLevelSuc(left, "hide_right", rhs);
        NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();

        left = ReplayTools.applyNoSplitTopLevelAntec(left, "notLeft", seqForm);

        seqForm = ReplayTools.getLastAddedSuc(left);

        // TODO: better count up to arity, however, extracting the original SMT arity of "or" is
        //  pretty difficult
        //  pragmatic solution: will always find the searched literal
        //int arity = extractOrArity(ctx.proofsexpr(0));
        //for (int i = 0; i < arity; i++) {
        while (seqForm.formula().op() == Junctor.OR) {

            left = ReplayTools.applyNoSplitTopLevelSuc(left, "orRight", seqForm);

            seqForm = ReplayTools.getLastAddedSuc(left, 1);
            SequentFormula split = ReplayTools.getLastAddedSuc(left, 0);

            if (split.formula().op() == Junctor.NOT) {
                left = ReplayTools.applyNoSplitTopLevelSuc(left, "notRight", split);
            } else {
                left = ReplayTools.applyNoSplitTopLevelSuc(left, "notElimRight", split);
            }

            // early close if possible
            split = ReplayTools.getLastAddedAntec(left);
            if (split.formula().equals(rhs.formula())) {
                // found the literal -> close
                // reinsert original rhs
                left = left.apply(insertRule).head();
                left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", split);
                break;
            } else if (ReplayTools.eqDifferentPolarity(seqForm, rhs)) {
                // additional check necessary for pragmatic solution, see e.g. sequent
                // !((p | q) | p) ==> !(p | q)
                if (seqForm.formula().op() == Junctor.NOT) {
                    left = left.apply(insertRule).head();
                    left = ReplayTools.applyNoSplitTopLevelAntec(left, "notRight", seqForm);
                    seqForm = ReplayTools.getLastAddedAntec(left);
                    left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
                } else if (rhs.formula().op() == Junctor.NOT) {
                    left = left.apply(insertRule).head();
                    left = ReplayTools.applyNoSplitTopLevelAntec(left, "notElimRight", seqForm);
                    seqForm = ReplayTools.getLastAddedAntec(left);
                    left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
                }
            }
        }

        if (!left.node().isClosed()) {
            if (seqForm.formula().op() == Junctor.NOT) {
                left = ReplayTools.applyNoSplitTopLevelSuc(left, "notRight", seqForm);
            } else {
                left = ReplayTools.applyNoSplitTopLevelSuc(left, "notElimRight", seqForm);
            }
            seqForm = ReplayTools.getLastAddedAntec(left);
            // now closing must be possible (or there is something wrong)
            // reinsert original rhs
            left = left.apply(insertRule).head();
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayMonotonicity(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        Goal left = goals.get(1);
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
                left = left.apply(app).head();
                seqForm = left.sequent().antecedent().get(0);
                params++;
            }

            // apply equalities
            for (int i = 0; i < params; i++) {

                // TODO: =
                //seqForm = left.sequent().succedent().get(0);
                //pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0).down(i), false);
                //app = ReplayTools.createTacletApp("applyEq", pio, left);
                //left = left.apply(app).head();

                // <->
                seqForm = left.sequent().antecedent().get(i);
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = ReplayTools.createTacletApp("insert_eqv_once_lr", pio, left);
                left = left.apply(app).head();


                seqForm = left.sequent().succedent().get(0);
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0).down(i), false);
                //app = ReplayTools.createTacletApp("insert_eqv", pio, left);
                // TODO: is there always only one locally introduced rule?
                Iterable<NoPosTacletApp> localRules = left.node().getLocalIntroducedRules();
                app = localRules.iterator().next();
                app = ReplayTools.autoInst(app, pio, left);
                left = left.apply(app).head();
            }

            // TODO: =
            //seqForm = left.sequent().succedent().get(0);
            //pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            //app = ReplayTools.createTacletApp("eqClose", pio, left);
            //left = left.apply(app).head();

            // <->
            seqForm = left.sequent().succedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            app = ReplayTools.createTacletApp("eq_eq", pio, left);
            left = left.apply(app).head();

            seqForm = left.sequent().succedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            app = ReplayTools.createTacletApp("closeTrue", pio, left);
            left = left.apply(app).head();
        } catch (Exception e) {
            // we show the exception, but only on cli
            e.printStackTrace();
            // revert the replay attempt and try to close automatically
            pruneTarget.proof().pruneProof(pruneTarget);
            goal = pruneTarget.proof().getGoal(pruneTarget);
            ReplayTools.runAutoMode(goal);
        }
        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }
    private void replayUnitResolution(ProofsexprContext ctx) {
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
            return;
        }

        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);

        // first child is a | b | ...
        // last child is conclusion (maybe false)
        // others are unit clauses
        int unitClauseCount = ctx.proofsexpr().size() - 2;

        // two cases:
        // 1. conclusion is false (in this case we derive false in the antecedent)
        // 2. conclusion is literal (in this case we derive the conclusion from the first clause)
        if (conclusion.equals(services.getTermBuilder().ff())) {
            replayUnitResFalseHelper(left, unitClauseCount);
        } else {
            replayUnitResLiteralHelper(left, unitClauseCount);
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
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

    // unit resolution where the succedent is a literal that is not "false"
    private void replayUnitResLiteralHelper(Goal left, int unitClauseCount) {
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

    private boolean isPosLiteral(Term formula) {
        return !formula.op().equals(Junctor.NOT);
    }
    /**
     * Splits the formula at the right side of a cut into the different antecedents of a rule and
     * starts replay of the corresponding subtrees.
     *
     * @param ctx
     */
    private void replayRightSideHelper(ProofsexprContext ctx) {

        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        SequentFormula cutFormula = sci.addedFormulas(false).head();
        if (cutFormula == null) {
            cutFormula = sci.modifiedFormulas(false).head().getNewFormula();
        }

        goal = ReplayTools.focus(cutFormula, goal, false);

        PosInOccurrence pio;
        TacletApp app;

        // last is succedent, others are subterms
        int antecCount = ctx.proofsexpr().size() - 1;
        System.out.println("Found " + ReplayTools.getOriginalText(ctx));
        System.out.println("  Arity is " + antecCount);

        for (int i = antecCount - 1; i > 0; i--) {
            pio = new PosInOccurrence(cutFormula, PosInTerm.getTopLevel(), false);
            app = ReplayTools.createTacletApp("andRight", pio, goal);
            List<Goal> antecs = goal.apply(app).toList();

            goal = antecs.get(0);
            visit(ctx.proofsexpr(i));

            goal = antecs.get(1);
            sci = goal.node().getNodeInfo().getSequentChangeInfo();
            cutFormula = sci.addedFormulas().head();
        }
        visit(ctx.proofsexpr(0));
    }

    private void replayTransStar(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        // trans* rule contains multiple transitivity and symmetry steps,
        // therefore we need auto mode here (however, should be really simple to close)
        ReplayTools.runAutoModePropositional(goal, 50);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }
    private void replayTrans(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        Goal left = goals.get(1);
        SequentFormula seqForm = goal.sequent().antecedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = ReplayTools.createTacletApp("andLeft", pio, left);
        left = left.apply(app).head();

        seqForm = left.sequent().antecedent().get(1);
        // TODO: other operators
        //if (seqForm.formula().op().equals(Junctor.IMP)) { ... }
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = ReplayTools.createTacletApp("insert_eqv_once_lr", pio, left);
        left = left.apply(app).head();

        NoPosTacletApp insertEqv = ReplayTools.findLocalRule("insert_eqv", left);
        seqForm = left.sequent().antecedent().get(0);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(1), true);
        app = ReplayTools.autoInst(insertEqv, pio, left);
        left = left.apply(app).head();

        seqForm = left.sequent().antecedent().get(0);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = ReplayTools.createTacletApp("closeAntec", pio, left);
        left = left.apply(app).head();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayMp(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        ////////////////////////////////////////////////////////////////////////////////////////////
        // left: and_left, replace_known_left, concrete_impl, close
        Goal left = goals.get(1);

        SequentFormula seqForm = ReplayTools.getLastAddedAntec(left);
        left = ReplayTools.applyNoSplitTopLevelAntec(left, "andLeft", seqForm);

        seqForm = ReplayTools.getLastAddedAntec(left);
        left = ReplayTools.applyNoSplitPosAntec(left, "replace_known_left",
            PosInTerm.getTopLevel().down(0), seqForm);

        seqForm = ReplayTools.getLastModifiedAntec(left);
        left = ReplayTools.applyNoSplitTopLevelAntec(left, "concrete_eq_1", seqForm);

        // Two cases: Is the last changed formula "false" or not?
        SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
        FormulaChangeInfo fci = sci.modifiedFormulas(true).head();
        // bugfix: NPE if sequence is: a, a <-> a ==> a
        //Term newTerm = fci.getNewFormula().formula();
        if (fci != null && fci.getNewFormula().formula().equals(services.getTermBuilder().ff())) {
            // 1. case: Gamma, false ==> Delta
            //   in this case apply closeFalse (used for final refutation of proof)
            seqForm = ReplayTools.getLastModifiedAntec(left);
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeFalse", seqForm);
        } else {
            // 2. case: Gamma, f ==> Delta, f
            //   in this case apply closeAntec
            seqForm = ReplayTools.getLastModifiedAntec(left);
            left = ReplayTools.applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
        }

        assert left.node().isClosed();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayLemma(ProofsexprContext ctx) {
        // note: connected to hypothesis rule, see method replayHypothesis()
        List<Term> hypotheses = extractHypotheses(ctx);

        assert hypotheses.size() >= 1;

        TermBuilder tb = services.getTermBuilder();
        Term cutTerm = hypotheses.get(0);
        for (int i = 1; i < hypotheses.size(); i++) {
            Term h = hypotheses.get(i);
            cutTerm = tb.and(cutTerm, h);
        }

        // apply cut
        TacletApp cutApp = ReplayTools.createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(cutApp).toList();
        Goal left = goals.get(1);

        // todo: really simple steps on the original conlcusion
        // orRight (n-1 times)
        // notRight (n times)
        // replace_known_left (n times)
        // concrete_and_ (n-1 times)
        // close
        ReplayTools.runAutoMode(left);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);

        // split and (andRight n-1 times)
        SequentFormula sf = ReplayTools.getLastAddedAntec(goal);
        for (int i = 0; i < hypotheses.size() - 1; i++) {
            goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "andRight", sf);
            sf = ReplayTools.getLastModifiedAntec(goal);
        }

        // hide hypotheses and remember the mapping to insert_taclets
        for (Term h : hypotheses) {
            SequentFormula hf = new SequentFormula(h);
            PosInOccurrence pio = new PosInOccurrence(hf, PosInTerm.getTopLevel(), true);
            TacletApp hide = ReplayTools.createTacletApp("hide_left", pio, goal);
            goal = goal.apply(hide).head();
            NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();
            hypoTaclets.put(h, insertRule);
        }
        // no we have the hypotheses available as taclets and descend further
        replayRightSideHelper(ctx);

        // since we leave this subtree now, hypotheses are no longer available
        for (Term h : hypotheses) {
            hypoTaclets.remove(h);
        }
    }

    // helper method for replayLemma()
    private List<Term> extractHypotheses(ProofsexprContext ctx) {
        // format: (or !h0 !h1 ... !hn)
        List<Term> hypotheses = new ArrayList<>();
        NoprooftermContext conclCtx = extractRuleConclusionCtx(ctx).noproofterm();
        int hypoCount = conclCtx.noproofterm().size() - 1;
        Term rest = extractRuleConclusion(ctx);

        for (int i = 0; i < hypoCount - 1; i++) {
            Term notH = rest.sub(1);
            // TODO: negation necessary if positive?
            assert notH.op() == Junctor.NOT;
            Term h = notH.sub(0);
            hypotheses.add(h);
            rest = rest.sub(0);
        }
        hypotheses.add(rest);
        return hypotheses;
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////// closing rules /////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////

    private void replayHypothesis(ProofsexprContext ctx) {
        // note: connected to lemma rule, see method replayLemma()
        Term hypothesis = extractRuleConclusion(ctx);

        if (hypoTaclets.get(hypothesis) != null) {
            throw new IllegalStateException("Hypothesis is not discharged by lemma rule: "
                + hypothesis);
        }
        NoPosTacletApp t = hypoTaclets.get(hypothesis);
        goal = goal.apply(t).head();

        // TODO: similar to asserted rule: more reasoning steps included (i.e. auto mode needed)?
        SequentFormula sf = ReplayTools.getLastAddedAntec(goal);
        goal = ReplayTools.applyNoSplitTopLevelAntec(goal, "closeAntec", sf);
    }

    private void replayIffEquisat(ProofsexprContext ctx) {
        // TODO is this correct?
        // nothing to do here, since we replace all ~ using <-> and epsilon when building terms
        // directly descend into antecedent
        replayRightSideHelper(ctx);
    }

    // assumption: sequent only single formula in succedent (antecedent should be empty)
    private void replayTrue(ProofsexprContext ctx) {
        SequentFormula seqForm = goal.sequent().succedent().getFirst();
        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "closeTrue", seqForm);
    }


    private void replayQuantInst(ProofsexprContext ctx) {
        // should be: orRight, notRight, instAll, close
        SequentFormula seqForm = goal.sequent().succedent().getFirst();

        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "orRight", seqForm);
        seqForm = ReplayTools.getLastAddedSuc(goal, 0);
        SequentFormula quant = ReplayTools.getLastAddedSuc(goal, 1);

        goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "notRight", quant);
        quant = ReplayTools.getLastAddedAntec(goal);

        // TODO: does only work with quantifiers with single bound variable
        List<PosInTerm> qvPositions = collectQvPositions(quant.formula());

        if (qvPositions.isEmpty()) {
            throw new IllegalStateException("Must not happen, error!");
        } else {
            PosInTerm qvPos = qvPositions.get(0);

            TacletApp app = goal.indexOfTaclets().lookup("instAll");
            System.out.println("Creating TacletApp instAll");

            Services services = goal.proof().getServices();
            app = app.setPosInOccurrence(new PosInOccurrence(seqForm, qvPos, false), services);

            // automatically find instantiations for matching find term
            TacletMatcher matcher = app.taclet().getMatcher();
            MatchConditions current = app.matchConditions();
            Term inst = qvPos.getSubTerm(seqForm.formula());
            MatchConditions mc = matcher.matchFind(inst, current, services);
            app = app.setMatchConditions(mc, services);

            // automatically find formulas for matching assume
            app = app.findIfFormulaInstantiations(goal.sequent(), services).head();
            goal = goal.apply(app).head();

            // close goal
            seqForm = ReplayTools.getLastAddedAntec(goal);
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "close", seqForm);
        }
    }

    // TODO: Use the epsilon definition taclet, this should drastically shorten the code here!
    private void replaySk(ProofsexprContext ctx) {
        // equiv_right
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        SequentFormula seqForm = sci.addedFormulas(false).head();
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp app = ReplayTools.createTacletApp("equiv_right", pio, goal);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);

        // collect all positions of the quantified variable in ex term
        // <-> positions of ifEx term in right side formula
        ProofsexprContext equiSat = ctx.proofsexpr(0);
        NoprooftermContext exCtx = equiSat.noproofterm().noproofterm(1);
        Term ex = new DefCollector(smtReplayer, services).visit(exCtx);
        List<PosInTerm> pits = collectQvPositions(ex);

        // pullOut ifEx term
        sci = left.node().getNodeInfo().getSequentChangeInfo();
        seqForm = sci.addedFormulas(false).head();
        PosInTerm firstPit = pits.get(0);
        pio = new PosInOccurrence(seqForm, firstPit, false);
        app = ReplayTools.createTacletApp("pullOut", pio, left);
        app = app.tryToInstantiate(services.getOverlay(left.getLocalNamespaces()));
        left = left.apply(app).head();

        sci = left.node().getNodeInfo().getSequentChangeInfo();
        SequentFormula ifExPulledOut = sci.addedFormulas(true).head();

        // applyEqRigid on every occurrence of ifEx term (pits)
        // except first one (was already pulled out)
        for (int i = 1; i < pits.size(); i++) {
            PosInTerm pit = pits.get(i);
            sci = left.node().getNodeInfo().getSequentChangeInfo();
            seqForm = sci.modifiedFormulas(false).head().getNewFormula();
            pio = new PosInOccurrence(seqForm, pit, false);
            app = ReplayTools.createTacletApp("applyEqRigid", pio, left);
            left = left.apply(app).head();
        }

        // ifExthenelsesplit
        PosInTerm ifExPit = PosInTerm.getTopLevel().down(0);
        pio = new PosInOccurrence(ifExPulledOut, ifExPit, true);
        TacletFilter ifExSplitFilter = new TacletFilter() {
            @Override
            protected boolean filter(Taclet taclet) {
                return taclet.name().equals(new Name("ifExthenelse1_split"));
            }
        };
        app = left.ruleAppIndex().getTacletAppAt(ifExSplitFilter, pio, services).head();
        app = app.tryToInstantiate(services.getOverlay(left.getLocalNamespaces()));
        List<Goal> ifExGoals = left.apply(app).toList();
        left = ifExGoals.get(1);

        // applyEqRigid on every occurrence of skolem variable
        for (int i = 0; i < pits.size(); i++) {
            sci = left.node().getNodeInfo().getSequentChangeInfo();
            if (i == 0) {
                seqForm = sci.addedFormulas(true).head();
            } else {
                seqForm = sci.modifiedFormulas(true).head().getNewFormula();
            }
            pio = new PosInOccurrence(seqForm, pits.get(i), true);
            app = ReplayTools.createTacletApp("applyEqRigid", pio, left);
            left = left.apply(app).head();
        }

        // close
        sci = left.node().getNodeInfo().getSequentChangeInfo();
        seqForm = sci.modifiedFormulas(true).head().getNewFormula();
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = ReplayTools.createTacletApp("closeAntec", pio, left);
        left = left.apply(app).head();

        //////////////////////////////////////////////////////////
        // close
        Goal right = ifExGoals.get(0);
        sci = right.node().getNodeInfo().getSequentChangeInfo();
        seqForm = sci.addedFormulas(false).head();
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        app = ReplayTools.createTacletApp("close", pio, right);
        right = right.apply(app).head();

        ////////////////////////////////////////////////////////////////////////////////////////////

        // instEx
        right = goals.get(0);
        sci = right.node().getNodeInfo().getSequentChangeInfo();
        seqForm = sci.addedFormulas(false).head();
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);

        TacletFilter exRightFilter = new TacletFilter() {
            @Override
            protected boolean filter(Taclet taclet) {
                return taclet.name().equals(new Name("exRight"));
            }
        };
        Services locServ = services.getOverlay(right.getLocalNamespaces());
        app = right.ruleAppIndex().getFindTaclet(exRightFilter, pio, locServ).head();
        SchemaVariable t = app.uninstantiatedVars().iterator().next();
        Term phiX = sci.addedFormulas(true).head().formula();
        Term inst = pits.get(0).getSubTerm(phiX);
        app = app.setPosInOccurrence(pio, locServ);
        app = app.addCheckedInstantiation(t, inst, locServ, true);


        right = right.apply(app).head();

        // close
        sci = right.node().getNodeInfo().getSequentChangeInfo();
        seqForm = sci.addedFormulas(false).head();
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        app = ReplayTools.createTacletApp("close", pio, right);
        right = right.apply(app).head();
    }

    private void replayAsserted(ProofsexprContext ctx) {
        // get sequentFormula, get corresponding insert_taclet from map, apply
        SequentFormula seqForm = goal.sequent().succedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);

        // two possible choices:
        TacletApp app = smtReplayer.getInsertTacletForSF(seqForm);
        Term negTerm = services.getTermBuilder().not(seqForm.formula());
        SequentFormula negForm = new SequentFormula(negTerm);
        TacletApp notApp = smtReplayer.getInsertTacletForSF(negForm);

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
        }
    }

    private void replayThLemma(ProofsexprContext ctx) {
        int arity = ctx.proofsexpr().size();

        // two cases: leaf rule or final rule in proof
        if (ctx.proofsexpr(arity - 1).getText().equals("false")) {
            // final rule
            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = ReplayTools.createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();
            // TODO: finish implementation
            throw new IllegalStateException("Not yet implemented: th-lemma as non-closing rule!");
        } else {
            // leaf rule
            ReplayTools.runAutoMode(goal);
        }
    }

    /**
     * Ensures that the top level symbol is not a symbol bound by let, but an actual context.
     * @param ctx the context which may or may not be a symbol bound by let
     * @return a context that is ensured not to be a symbol bound by let (however, subterms may
     *  contain other symbols again!)
     */
    private ParserRuleContext ensureLookup(ParserRuleContext ctx) {
        ParserRuleContext def = smtReplayer.getSymbolDef(ctx.getText(), ctx);
        if (def != null) {
            return ensureLookup(def);
        } else {
            return ctx;
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    /////////////////////////////////////// utility methods ////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////

    private Term lookupOrCreate(ProofsexprContext ctx) {
        // ctx could be:
        // - symbol from KeY (is in translation map)
        // - symbol bound via let
        // - a term with nested rule applications (descend into succedent of the rule)
        Term term = smtReplayer.getTranslationToTerm(ctx.getText());
        if (term == null) {
            // recursively descend into let definition
            ParserRuleContext letDef = smtReplayer.getSymbolDef(ctx.getText(), ctx);
            if (letDef != null) {
                term = letDef.accept(new DefCollector(smtReplayer, services));
            } else {
                // could be a term containing nested rule applications again
                term = ctx.accept(new DefCollector(smtReplayer, services));
            }
        }

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

    private ProofsexprContext extractRuleConclusionCtx(ProofsexprContext ctx) {
        return ctx.proofsexpr(ctx.proofsexpr().size() - 1);
    }

    private Term extractRuleConclusion(ProofsexprContext ctx) {
        ProofsexprContext conclusionCtx = extractRuleConclusionCtx(ctx);
        return lookupOrCreate(conclusionCtx);
    }

    private Term extractRuleAntecedents(ProofsexprContext ctx) {
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
                result = services.getTermFactory().createTerm(Junctor.AND, result, antecs.get(i));
            }
            return result;
        }
    }
}
