package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.FormulaChangeInfo;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;
import org.antlr.v4.runtime.Token;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.List;

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
        System.out.println(rulename);
        goal.node().getNodeInfo().setNotes(rulename);

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
        default:
            throw new IllegalStateException("Replay for rule not yet implemented: " + rulename);
        }
        //return super.visitProofsexpr(ctx);
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
        SMTProofParser.NoprooftermContext exCtx = equiSat.noproofterm().noproofterm(1);
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
        // TODO: what about goal?
    }

    private List<PosInTerm> collectQvPositions(Term ex) {
        QuantifiableVariable qv = ex.boundVars().last(); // there is exact one by construction
        return collectQvPositionsRec(qv, ex.sub(0), PosInTerm.getTopLevel());
    }

    private List<PosInTerm> collectQvPositionsRec(QuantifiableVariable qv,
                                                  Term subTerm, PosInTerm prefix) {
        List<PosInTerm> result = new ArrayList<>();
        if (subTerm.op() instanceof QuantifiableVariable
            && SMTReplayer.equalsOp((QuantifiableVariable) subTerm.op(), qv)) {
            result.add(prefix);
        } else {
            for (int i = 0; i < subTerm.subs().size(); i++) {
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

    private void replayNotOrElim(ProofsexprContext ctx) {
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();
        Goal left = goals.get(1);
        SequentFormula orig = left.sequent().succedent().get(0);

        SequentFormula seqForm = left.sequent().antecedent().get(0);
        PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("notLeft", pio, left);
        left = left.apply(app).head();

        // orRight
        seqForm = left.sequent().succedent().get(0);
        // better count up to arity
        for (int i = 0; i < ctx.proofsexpr().size(); i++) {
            //while (seqForm.formula().op() == Junctor.OR) {
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            app = createTacletApp("orRight", pio, left);
            left = left.apply(app).head();
            //seqForm = left.sequent().succedent().get(0);
            SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
            // TODO: is the order of the added formulas deterministic?
            seqForm = sci.addedFormulas().tail().head();
            if (seqForm == null) {
                // attention: the formula may be equal to the original one by chance
                break;
            }
        }

        pio = new PosInOccurrence(orig, PosInTerm.getTopLevel(), false);
        if (orig.formula().op() == Junctor.NOT) {
            app = createTacletApp("notRight", pio, left);
        } else {
            // TODO: additional rule (not in standard taclets!)
            app = createTacletApp("notElimRight", pio, left);
        }
        left = left.apply(app).head();

        seqForm = left.sequent().antecedent().get(0);
        pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
        app = createTacletApp("closeAntec", pio, left);
        left = left.apply(app).head();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
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
        Term cutTerm = extractRuleAntecedents(ctx);
        TacletApp app = createCutApp(goal, cutTerm);
        List<Goal> goals = goal.apply(app).toList();

        // last child is succedent, first child is a | b | ..., others are unit clauses
        int unitClauseCount = ctx.proofsexpr().size() - 2;

        Goal left = goals.get(1);
        SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();

        SequentFormula seqForm = sci.addedFormulas().head();

        // split unit clauses from cut formula
        PosInOccurrence pio;
        SequentFormula clause = null;
        List<SequentFormula> unitClauses = new ArrayList<>();
        for (int i = 0; i < unitClauseCount; i++) {
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("andLeft", pio, left);
            left = left.apply(app).head();
            sci = left.node().getNodeInfo().getSequentChangeInfo();
            // TODO: is the order of the added formulas deterministic?
            seqForm = sci.addedFormulas().tail().head();
            unitClauses.add(sci.addedFormulas().head());

            // the clause a | b | ... is the last one remaining after the split
            clause = seqForm;
        }

        // for every unit clause: apply notLeft
        for (SequentFormula unitClause : unitClauses) {
            pio = new PosInOccurrence(unitClause, PosInTerm.getTopLevel(), true);
            app = createTacletApp("notLeft", pio, left);
            left = left.apply(app).head();
            sci = left.node().getNodeInfo().getSequentChangeInfo();
        }

        if (unitClauseCount > 1) {
            for (int i = 0; i < unitClauseCount; i++) {
                // TODO: order and clause count may differ
                if (i == unitClauseCount - 1) {
                    // different position for last unit clause!
                    pio = new PosInOccurrence(clause, PosInTerm.getTopLevel(), true);
                } else {
                    pio = new PosInOccurrence(clause, PosInTerm.getTopLevel().down(0), true);
                }
                app = createTacletApp("replace_known_right", pio, left);
                left = left.apply(app).head();

                sci = left.node().getNodeInfo().getSequentChangeInfo();
                clause = sci.modifiedFormulas().head().getNewFormula();

                // not necessary for last clause!
                if (i != unitClauseCount - 1) {
                    pio = new PosInOccurrence(clause, PosInTerm.getTopLevel(), true);
                    app = createTacletApp("concrete_or_2", pio, left);
                    left = left.apply(app).head();

                    sci = left.node().getNodeInfo().getSequentChangeInfo();
                    clause = sci.modifiedFormulas().head().getNewFormula();
                }
            }
            pio = new PosInOccurrence(clause, PosInTerm.getTopLevel(), true);
            app = createTacletApp("closeFalse", pio, left);
            left = left.apply(app).head();
        } else {    // unitClauseCount == 1
            pio = new PosInOccurrence(clause, PosInTerm.getTopLevel(), true);
            app = createTacletApp("closeAntec", pio, left);
            left = left.apply(app).head();
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
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
        Term newTerm = fci.getNewFormula().formula();
        if (newTerm.equals(services.getTermBuilder().ff())) {
            // 1. case: Gamma, false ==> Delta
            //   in this case apply closeFalse (used for final refutation of proof)
            seqForm = left.sequent().antecedent().get(1);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("closeFalse", pio, left);
            left = left.apply(app).head();
        } else {
            // 2. case: Gamma, f ==> Delta, f
            //   in this case apply closeAntec
            seqForm = left.sequent().antecedent().get(1);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("closeAntec", pio, left);
            left = left.apply(app).head();
        }

        assert left.node().isClosed();

        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
    }

    @Override
    public Void visitIdentifier(SMTProofParser.IdentifierContext ctx) {
        ProofsexprContext def = smtReplayer.getSymbolDef(ctx.getText());
        if (def != null) {
            // continue proof replay with the partial tree from the symbol table
            visit(def);
        }
        return null;
    }

    private Term lookupOrCreate(ProofsexprContext ctx) {
        // child could be:
        // - symbol from KeY (is in translation map)
        // - symbol bound via let
        // - a term with nested rule applications
        Term term = smtReplayer.getTranslationToTerm(ctx.getText());
        if (term == null) {
            // recursively descend into let definition
            ProofsexprContext letDef = smtReplayer.getSymbolDef(ctx.getText());
            if (letDef != null) {
                term = letDef.accept(new DefCollector(smtReplayer, services));
            } else {
                // could be a term containing nested rule applications again
                term = ctx.accept(new DefCollector(smtReplayer, services));
            }
        }
        return term;
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

        assert app.complete();
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
