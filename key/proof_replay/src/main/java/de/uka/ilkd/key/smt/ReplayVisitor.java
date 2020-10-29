package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.FormulaChangeInfo;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.smt.SMTProofParser.IdentifierContext;
import de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

class ReplayVisitor extends SMTProofBaseVisitor<Void> {
    private final SMTReplayer smtReplayer;
    private Goal goal;
    private final Services services;

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
        System.out.println(SMTReplayer.getOriginalText(ctx));
        goal.node().getNodeInfo().setNotes(SMTReplayer.getOriginalText(ctx));

        switch (rulename) {
        case "asserted":
            //runAutoMode(goal, true);
            replayAsserted(ctx);
            return null;
        case "rewrite":
            replayRewrite(ctx);
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
        case "not-or-elim":
            replayNotOrElim(ctx);
            return null;
        case "and-elim":
            replayAndElim(ctx);
            return null;
        case "mp":
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
            replayBind(ctx);
            return null;
        case "def-axiom":
            replayDefAxiom(ctx);
            return null;
        case "quant-inst":
            replayQuantInst(ctx);
            return null;
        default:
            System.out.println("Replay for rule not yet implemented: " + rulename);
            //throw new IllegalStateException("Replay for rule not yet implemented: " + rulename);
            return null;
        }
        //return super.visitProofsexpr(ctx);
    }

    private void replayQuantInst(ProofsexprContext ctx) {
        // should be: orRight, notRight, instAll, close
        SequentFormula seqForm = goal.sequent().succedent().getFirst();

        goal = applyNoSplitTopLevelSuc(goal, "orRight", seqForm);
        seqForm = getLastAddedSuc(goal, 0);
        SequentFormula quant = getLastAddedSuc(goal, 1);

        goal = applyNoSplitTopLevelSuc(goal, "notRight", quant);
        quant = getLastAddedAntec(goal);

        // TODO: does only work with quantifiers with single bound variable
        List<PosInTerm> qvPositions = collectQvPositions(quant.formula());

        // may happen due to typeguard, which is skipped by the translation
        if (qvPositions.isEmpty()) {
            // TODO: rule does not work if typeguard is not implemented
            //  (typeguard <-> instanceof can not be proven)
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
            seqForm = getLastAddedAntec(goal);
            goal = applyNoSplitTopLevelSuc(goal, "close", seqForm);
        }
    }

    private void replayDefAxiom(ProofsexprContext ctx) {
        // closing rule (Tseitin axioms)
        // quick and dirty solution: use auto mode (simple propositional steps)
        // TODO: implement schemas
        // TODO: run auto mode with specific ruleset?
        runAutoMode(goal);
    }

    private void replayBind(ProofsexprContext ctx) {
        if (!ctx.proofsexpr(0).noproofterm().func.getText().equals("lambda")) {
            throw new IllegalStateException("Error! After 'proof-bind', 'lambda' is expected!");
        }

        // could be a symbol bound by let
        ProofsexprContext child = ctx.proofsexpr(0);
        ParserRuleContext letDef = smtReplayer.getSymbolDef(child.getText(), child);
        if (letDef != null) {
            // child is var name, letDef is (lambda ...)
            // TODO: check instanceof
            ProofsexprContext lambdaScope = ((ProofsexprContext)letDef).proofsexpr(0);
            // TODO: add variables to scope?
            visit(lambdaScope);
        } else {
            // child is term (lambda ...)
            ProofsexprContext lambdaScope = child.proofsexpr(0);
            // TODO: add variables to scope?
            visit(lambdaScope);
        }
    }

    // sequent: ==> A = A
    private void replayRefl(ProofsexprContext ctx) {
        SequentFormula seqForm = goal.sequent().succedent().getFirst();
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp app = createTacletApp("eqClose", pio, goal);
        goal = goal.apply(app).head();

        seqForm = goal.sequent().succedent().getFirst();
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        app = createTacletApp("closeTrue", pio, goal);
        goal = goal.apply(app).head();
        // goal is closed now!
    }

    // sequent: ==> A = B
    private void replaySymm(ProofsexprContext ctx) {
        // TODO: we do not check that the premise of the rule is really the symmetric formula
        // TODO: we assume there is only a single formula in succedent
        SequentFormula seqForm = goal.sequent().succedent().getFirst();
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp app = createTacletApp("eqSymm", pio, goal);
        goal = goal.apply(app).head();
    }

    // sequent: ==> Qx. phi(x) <-> Qx. psi(x)
    private void replayQuantIntro(ProofsexprContext ctx) {
        // cut: forall x. phi(x) <-> psi(x)
        // TODO: on the right side there may be an ~ (which is converted to <->), <-> or =
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);

        // equiv_right
        SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
        SequentFormula seqForm = sci.addedFormulas(false).head();
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        app = createTacletApp("equiv_right", pio, left);
        List<Goal> goalsEquiv = left.apply(app).toList();
        ////////////////////////////////////////////////////////////////
        Goal equivLeft = goalsEquiv.get(1);

        // exLeft (skolemize)
        sci = equivLeft.node().getNodeInfo().getSequentChangeInfo();
        seqForm = sci.addedFormulas(true).head();
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("exLeft", pio, equivLeft);
        equivLeft = equivLeft.apply(app).head();

        IProgramVariable pv = equivLeft.node().getLocalProgVars().head();

        ////////////////////////////////////////////////////////////////

        ////////////////////////////////////////////////////////////////////////////////////////////

        goal = goals.get(0);
        visit(ctx.proofsexpr(0));
    }

    private void replaySk(ProofsexprContext ctx) {
        // equiv_right
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        SequentFormula seqForm = sci.addedFormulas(false).head();
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp app = createTacletApp("equiv_right", pio, goal);
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
        app = createTacletApp("pullOut", pio, left);
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
            app = createTacletApp("applyEqRigid", pio, left);
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
            app = createTacletApp("applyEqRigid", pio, left);
            left = left.apply(app).head();
        }

        // close
        sci = left.node().getNodeInfo().getSequentChangeInfo();
        seqForm = sci.modifiedFormulas(true).head().getNewFormula();
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("closeAntec", pio, left);
        left = left.apply(app).head();

        //////////////////////////////////////////////////////////
        // close
        Goal right = ifExGoals.get(0);
        sci = right.node().getNodeInfo().getSequentChangeInfo();
        seqForm = sci.addedFormulas(false).head();
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        app = createTacletApp("close", pio, right);
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
        app = createTacletApp("close", pio, right);
        right = right.apply(app).head();
    }

    private List<PosInTerm> collectQvPositions(Term quant) {
        QuantifiableVariable qv = quant.boundVars().last(); // TODO: there has to be exactly one!
        return collectQvPositionsRec(qv, quant.sub(0), PosInTerm.getTopLevel());
    }

    private List<PosInTerm> collectQvPositionsRec(QuantifiableVariable qv,
                                                  Term subTerm, PosInTerm prefix) {
        List<PosInTerm> result = new ArrayList<>();
        if (subTerm.op() instanceof QuantifiableVariable
            && SMTReplayer.equalsOp((QuantifiableVariable) subTerm.op(), qv)) {
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

    private void replayThLemma(ProofsexprContext ctx) {
        int arity = ctx.proofsexpr().size();

        // two cases: leaf rule or final rule in proof
        if (ctx.proofsexpr(arity - 1).getText().equals("false")) {
            // final rule
            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();
            // TODO: finish implementation
        } else {
            // leaf rule
            runAutoMode(goal);
        }
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
                app = createTacletApp("notRight", pio, goal);
                goal = goal.apply(app).head();

                SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
                SequentFormula addedAntec = sci.addedFormulas(true).head();
                pio = new PosInOccurrence(addedAntec, PosInTerm.getTopLevel(), true);
                app = createTacletApp("closeAntec", pio, goal);
                goal = goal.apply(app).head();
            }
        } else {
            //throw new IllegalStateException("The formula " + seqForm.formula() + " is not an assertion!");
            System.out.println("The formula " + seqForm.formula() + " is not found as assertion!");
            //System.out.println("Starting auto mode ...");
            // TODO: insert matching assertion (how to find?)
        }
    }

    private void replayRewrite(ProofsexprContext ctx) {
        if (goal.sequent().succedent().get(0).formula().op() == Equality.EQV) {
            // equiv_right top level to guide the prover
            SequentFormula seqForm = goal.sequent().succedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            TacletApp app = createTacletApp("equiv_right", pio, goal);
            List<Goal> goals = goal.apply(app).toList();
            // running automode separately on both goals increases success rate
            runAutoMode(goals.get(0));
            runAutoMode(goals.get(1));
        } else {
            runAutoMode(goal);
        }
    }

    private void replayIffTrue(ProofsexprContext ctx) {
        SequentFormula seqForm = goal.sequent().succedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp concreteEq3 = createTacletApp("concrete_eq_3", pio, goal);
        goal = goal.apply(concreteEq3).head();
        visit(ctx.proofsexpr(0));
    }

    private void replayIffFalse(ProofsexprContext ctx) {
        SequentFormula seqForm = goal.sequent().succedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        TacletApp concreteEq4 = createTacletApp("concrete_eq_4", pio, goal);
        goal = goal.apply(concreteEq4).head();
        visit(ctx.proofsexpr(0));
    }

    private void replayAndElim(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);
        SequentFormula orig = left.sequent().succedent().get(0);

        SequentFormula seqForm = left.sequent().antecedent().get(0);
        PosInOccurrence pio;

        int arity = ctx.proofsexpr().size();

        // special case for typeguard

        // this selects the text "typeguard" in the contraposition example
        //smtReplayer.getSymbolDef(ctx.proofsexpr(0).proofsexpr(ctx.proofsexpr(0).proofsexpr().size()-1).getText()).noproofterm().noproofterm(1).noproofterm(0).getText()

        for (int i = 0; i < arity; i++) {
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);

            // TODO: this case may occur for other rules as well
            if (!pio.subTerm().op().equals(Junctor.AND)) {
                // this may occur if a typeguard has been skipped by the translation
                break;
            }

            app = createTacletApp("andLeft", pio, left);
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
        app = createTacletApp("close", pio, left);
        left = left.apply(app).head();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    // notLeft, orRight ..., notRight, ..., closeAntec
    private void replayNotOrElim(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);
        SequentFormula rhs = left.sequent().succedent().get(0);
        SequentFormula seqForm = getLastAddedAntec(left);

        // to avoid cases where a temporary formula is equal to the conclusion
        // (and thus destroying all index calculations), we hide the original rhs here
        left = applyNoSplitTopLevelSuc(left, "hide_right", rhs);
        NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();

        left = applyNoSplitTopLevelAntec(left, "notLeft", seqForm);

        seqForm = getLastAddedSuc(left);

        // TODO: better count up to arity, however, extracting the original SMT arity of or is
        //  pretty difficult
        //  pragmatic solution: will always find the searched literal
        //int arity = extractOrArity(ctx.proofsexpr(0));
        //for (int i = 0; i < arity; i++) {
        while (seqForm.formula().op() == Junctor.OR) {

            left = applyNoSplitTopLevelSuc(left, "orRight", seqForm);

            seqForm = getLastAddedSuc(left, 1);
            SequentFormula split = getLastAddedSuc(left, 0);

            if (split.formula().op() == Junctor.NOT) {
                left = applyNoSplitTopLevelSuc(left, "notRight", split);
            } else {
                left = applyNoSplitTopLevelSuc(left, "notElimRight", split);
            }

            // early close if possible
            split = getLastAddedAntec(left);
            if (split.formula().equals(rhs.formula())) {
                // found the literal -> close
                // reinsert original rhs
                left = left.apply(insertRule).head();
                left = applyNoSplitTopLevelAntec(left, "closeAntec", split);
                break;
            } else {
                // additional checks necessary for pragmatic solution, see e.g. sequent
                // !((p | q) | p) ==> !(p | q)
                if (seqForm.formula().op() == Junctor.NOT) {
                    left = left.apply(insertRule).head();
                    left = applyNoSplitTopLevelAntec(left, "notRight", seqForm);
                    seqForm = getLastAddedAntec(left);
                    left = applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
                } else if (rhs.formula().op() == Junctor.NOT) {
                    left = left.apply(insertRule).head();
                    left = applyNoSplitTopLevelAntec(left, "notElimRight", seqForm);
                    seqForm = getLastAddedAntec(left);
                    left = applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
                }
            }
        }

        if (!left.node().isClosed()) {
            if (seqForm.formula().op() == Junctor.NOT) {
                left = applyNoSplitTopLevelSuc(left, "notRight", seqForm);
            } else {
                left = applyNoSplitTopLevelSuc(left, "notElimRight", seqForm);
            }
            seqForm = getLastAddedAntec(left);
            // now closing must be possible (or there is something wrong)
            // reinsert original rhs
            left = left.apply(insertRule).head();
            left = applyNoSplitTopLevelAntec(left, "closeAntec", seqForm);
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private boolean eqDifferentPolarity(Term t1, Term t2) {
        if (t1.op() == Junctor.NOT) {
            return t1.sub(0).equals(t2);
        } else if (t2.op() == Junctor.NOT) {
            return t2.sub(0).equals(t1);
        }
        return false;
    }

    private void replayMonotonicity(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);
        SequentFormula seqForm = left.sequent().antecedent().get(0);

        PosInOccurrence pio;

        int params = 1;

        // and left
        while (seqForm.formula().op() == Junctor.AND) {
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("andLeft", pio, left);
            left = left.apply(app).head();
            seqForm = left.sequent().antecedent().get(0);
            params++;
        }

        // apply equalities
        for (int i = 0; i < params; i++) {

            // TODO: =
            //seqForm = left.sequent().succedent().get(0);
            //pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0).down(i), false);
            //app = createTacletApp("applyEq", pio, left);
            //left = left.apply(app).head();

            // TODO: <->
            seqForm = left.sequent().antecedent().get(i);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("insert_eqv_once_lr", pio, left);
            left = left.apply(app).head();


            seqForm = left.sequent().succedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0).down(i), false);
            //app = createTacletApp("insert_eqv", pio, left);
            // TODO: is there always only one locally introduced rule?
            Iterable<NoPosTacletApp> localRules = left.node().getLocalIntroducedRules();
            app = localRules.iterator().next();
            app = autoInst(app, pio, left);
            left = left.apply(app).head();
        }

        // TODO: =
        //seqForm = left.sequent().succedent().get(0);
        //pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        //app = createTacletApp("eqClose", pio, left);
        //left = left.apply(app).head();

        // TODO: <->
        seqForm = left.sequent().succedent().get(0);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        app = createTacletApp("eq_eq", pio, left);
        left = left.apply(app).head();

        seqForm = left.sequent().succedent().get(0);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
        app = createTacletApp("closeTrue", pio, left);
        left = left.apply(app).head();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayUnitResolution(ProofsexprContext ctx) {
        Term conclusion = extractRuleConclusion(ctx);

        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);

        SequentFormula seqForm = getLastAddedAntec(left);    // = cut formula

        // first child is a | b | ...
        // last child is conclusion (maybe false)
        // others are unit clauses
        int unitClauseCount = ctx.proofsexpr().size() - 2;

        // two cases:
        // 1. conclusion is false (in this case we derive false in the antecedent)
        // 2. conclusion is literal (in this case we derive the conclusion from the first clause)
        if (conclusion.equals(services.getTermBuilder().ff())) {
            int literalCount = unitClauseCount;

            // split unit clauses from cutTerm, store them in list to find them again later
            List<SequentFormula> unitClauses = new ArrayList<>();
            for (int i = 0; i < unitClauseCount; i++) {
                left = applyNoSplitTopLevelAntec(left, "andLeft", seqForm);
                //unitClauses.add(getLastAddedAntec(left));
                unitClauses.add(getLastAddedAntec(left, 0));
                seqForm = getLastAddedAntec(left, 1);      // = rest of cut formula
            }

            // rest of original cut formula is the clause a | b | ... (contains all unit clauses)
            SequentFormula clause = seqForm;

            for (SequentFormula unitClause : unitClauses) {
                // bring unitClause to succedent
                if (isPosLiteral(unitClause.formula())) {           // apply notElimLeft
                    left = applyNoSplitTopLevelAntec(left, "notElimLeft", unitClause);
                } else {                                            // apply notLeft
                    left = applyNoSplitTopLevelAntec(left, "notLeft", unitClause);
                }
            }
            // note: two separate loops since order may differ
            for (int i = 0; i < unitClauseCount; i++) {
                if (i == unitClauseCount - 1) {
                    left = applyNoSplitTopLevelAntec(left, "replace_known_right", clause);
                } else {
                    // replace last unit clause in clause
                    PosInTerm secondParam = PosInTerm.getTopLevel().down(1);
                    left = applyNoSplitPosAntec(left, "replace_known_right", secondParam, clause);
                }
                clause = getLastModifiedAntec(left);

                if (i == unitClauseCount - 1) {
                    // last unit clause: clause = false now -> close branch
                    left = applyNoSplitTopLevelAntec(left, "closeFalse", clause);
                } else {
                    left = applyNoSplitTopLevelAntec(left, "concrete_or_4", clause);
                    clause = getLastModifiedAntec(left);
                }
            }
        } else {
            int literalCount = unitClauseCount + 1; // unit clauses and conclusion

            // split unit clauses from cutTerm, store them in list to find them again later
            List<SequentFormula> unitClauses = new ArrayList<>();
            for (int i = 0; i < unitClauseCount; i++) {
                left = applyNoSplitTopLevelAntec(left, "andLeft", seqForm);
                // conclusion should not be added to unit clause list
                if (!getLastAddedAntec(left).formula().equals(conclusion)) {
                    unitClauses.add(getLastAddedAntec(left, 0));
                }
                seqForm = getLastAddedAntec(left, 1);      // = rest of cut formula
            }

            // rest of original cut formula is the clause a | b | ... (contains all unit clauses)
            SequentFormula clause = seqForm;

            for (SequentFormula unitClause : unitClauses) {
                // bring unitClause to succedent
                if (isPosLiteral(unitClause.formula())) {           // apply notElimLeft
                    left = applyNoSplitTopLevelAntec(left, "notElimLeft", unitClause);
                } else {                                            // apply notLeft
                    left = applyNoSplitTopLevelAntec(left, "notLeft", unitClause);
                }
            }

            for (int i = 0; i < literalCount - 1; i++) {
                PosInTerm secondParam = PosInTerm.getTopLevel().down(1);
                left = applyNoSplitPosAntec(left, "replace_known_right", secondParam, clause);
                clause = getLastModifiedAntec(left);
                left = applyNoSplitTopLevelAntec(left, "concrete_or_4", clause);
                clause = getLastModifiedAntec(left);
            }

            // replace last unit clause in clause
            left = applyNoSplitTopLevelAntec(left, "replace_known_right", clause);
            clause = getLastModifiedAntec(left);
            // last literal: clause = false now -> close branch
            left = applyNoSplitTopLevelAntec(left, "closeFalse", clause);
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    //////////////////////// convenience methods (for taclet services?) ////////////////////////////

    private static SequentFormula getLastModifiedAntec(Goal goal) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.modifiedFormulas(true).head().getNewFormula();
    }

    private static SequentFormula getLastModifiedSuc(Goal goal) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.modifiedFormulas(false).head().getNewFormula();
    }

    private static SequentFormula getLastAddedAntec(Goal goal) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.addedFormulas(true).head();
    }

    private static SequentFormula getLastAddedAntec(Goal goal, int index) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.addedFormulas(true).toList().get(index);
    }

    private static SequentFormula getLastAddedSuc(Goal goal) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.addedFormulas(false).head();
    }

    private static SequentFormula getLastAddedSuc(Goal goal, int index) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.addedFormulas(false).toList().get(index);
    }

    private static Goal applyNoSplitPosAntec(Goal goal, String tacletName, PosInTerm pit,
                                             SequentFormula sf) {
        PosInOccurrence pio = new PosInOccurrence(sf, pit, true);
        TacletApp app = createTacletApp(tacletName, pio, goal);
        return goal.apply(app).head();
    }

    private static Goal applyNoSplitTopLevelAntec(Goal goal, String tacletName, SequentFormula sf) {
        PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), true);
        TacletApp app = createTacletApp(tacletName, pio, goal);
        return goal.apply(app).head();
    }

    private static Goal applyNoSplitTopLevelSuc(Goal goal, String tacletName, SequentFormula sf) {
        PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
        TacletApp app = createTacletApp(tacletName, pio, goal);
        return goal.apply(app).head();
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////

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

        goal = focus(cutFormula, goal, false);

        PosInOccurrence pio;
        TacletApp app;

        // last is succedent, others are subterms
        int antecCount = ctx.proofsexpr().size() - 1;
        System.out.println("Found " + SMTReplayer.getOriginalText(ctx));
        System.out.println("  Arity is " + antecCount);

        for (int i = antecCount - 1; i > 0; i--) {
            pio = new PosInOccurrence(cutFormula, PosInTerm.getTopLevel(), false);
            app = createTacletApp("andRight", pio, goal);
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
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        // trans* rule contains multiple transitivity and symmetry steps,
        // therefore we need auto mode here (however, should be really simple to close)
        runAutoMode(goal);

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayTrans(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        Goal left = goals.get(1);
        SequentFormula seqForm = goal.sequent().antecedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("andLeft", pio, left);
        left = left.apply(app).head();

        seqForm = left.sequent().antecedent().get(1);
        // TODO: other operators
        //if (seqForm.formula().op().equals(Junctor.IMP)) { ... }
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("insert_eqv_once_lr", pio, left);
        left = left.apply(app).head();

        NoPosTacletApp insertEqv = findLocalRule("insert_eqv", left);
        seqForm = left.sequent().antecedent().get(0);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(1), true);
        app = autoInst(insertEqv, pio, left);
        left = left.apply(app).head();

        seqForm = left.sequent().antecedent().get(0);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("closeAntec", pio, left);
        left = left.apply(app).head();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    private void replayMp(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        ////////////////////////////////////////////////////////////////////////////////////////////
        // left: and_left, replace_known_left, concrete_impl, close
        Goal left = goals.get(1);

        SequentFormula seqForm = left.sequent().antecedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("andLeft", pio, left);
        left = left.apply(app).head();

        seqForm = left.sequent().antecedent().get(1);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0), true);
        app = createTacletApp("replace_known_left", pio, left);
        left = left.apply(app).head();

        seqForm = left.sequent().antecedent().get(1);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("concrete_eq_1", pio, left);
        left = left.apply(app).head();

        // Two cases: Is the last changed formula "false" or not?
        SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
        FormulaChangeInfo fci = sci.modifiedFormulas(true).head();
        // bugfix: NPE if sequence is: a, a <-> a ==> a
        //Term newTerm = fci.getNewFormula().formula();
        if (fci != null && fci.getNewFormula().formula().equals(services.getTermBuilder().ff())) {
            // 1. case: Gamma, false ==> Delta
            //   in this case apply closeFalse (used for final refutation of proof)
            seqForm = left.sequent().antecedent().get(1);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("closeFalse", pio, left);
            left = left.apply(app).head();
        } else {
            // 2. case: Gamma, f ==> Delta, f
            //   in this case apply closeAntec
            //seqForm = left.sequent().antecedent().get(1);
            seqForm = left.sequent().succedent().getFirst();

            /*
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("close", pio, left);
            left = left.apply(app).head();*/

            left = applyNoSplitTopLevelSuc(left, "close", seqForm);
        }

        assert left.node().isClosed();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
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

    static TacletApp createTacletApp(String tacletName, PosInOccurrence pos, Goal goal) {
        TacletApp app = goal.indexOfTaclets().lookup(tacletName);
        System.out.println("Creating TacletApp " + tacletName);
        return autoInst(app, pos, goal);
    }

    // automatically instantiates taclet from PosInOccurrence, only works for taclets where all
    // instantiations are determined by the position
    private static TacletApp autoInst(TacletApp app, PosInOccurrence pos, Goal goal) {
        Services services = goal.proof().getServices();
        Term posTerm = pos.subTerm();
        app = app.setPosInOccurrence(pos, services);

        // automatically find instantiations for matching find term
        TacletMatcher matcher = app.taclet().getMatcher();
        // use app.matchConditions(): must not overwrite fixed instantiations (e.g. insert_hidden taclet)
        MatchConditions current = app.matchConditions();
        MatchConditions mc = matcher.matchFind(posTerm, current, services);
        app = app.setMatchConditions(mc, services);

        // automatically find formulas for matching assume
        app = app.findIfFormulaInstantiations(goal.sequent(), services).head();

        return app;
    }

    private static NoPosTacletApp createCutApp(Goal goal, Term cutFormula) {
        NoPosTacletApp app = goal.indexOfTaclets().lookup("cut");
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        // since all branches in addInstantiation return NoPosTacletApp, the cast should always be safe
        return (NoPosTacletApp) app.addInstantiation(sv, cutFormula, true, goal.proof().getServices());
    }

    private void runAutoMode(Goal goal) {
        // current notes could contain rule name -> append
        String currentNotes = goal.node().getNodeInfo().getNotes();
        if (currentNotes != null) {
            goal.node().getNodeInfo().setNotes(currentNotes + " automatic proof search");
        } else {
            goal.node().getNodeInfo().setNotes("automatic proof search");
        }

        TryCloseMacro close = new TryCloseMacro(50);
        try {
            close.applyTo(null, goal.proof(), ImmutableSLList.<Goal>nil().append(goal), null, null);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    private NoPosTacletApp findLocalRule(String namePrefix, Goal goal) {
        for (NoPosTacletApp app : goal.node().getLocalIntroducedRules()) {
            // TODO: there may be multiple rules with this prefix
            if (app.taclet().name().toString().startsWith(namePrefix)) {
                return app;
            }
        }
        return null;
    }

    private Goal focus(SequentFormula formula, Goal goal, boolean antec) {
        FocusRule focusRule = FocusRule.INSTANCE;
        PosInOccurrence pio = new PosInOccurrence(formula, PosInTerm.getTopLevel(), antec);
        RuleApp app = focusRule.createApp(pio, services);
        return goal.apply(app).head();
    }
}
