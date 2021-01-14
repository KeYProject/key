package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.util.Pair;
import org.antlr.v4.runtime.ParserRuleContext;

import java.util.Iterator;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class ProofBind extends ProofRule {
    public ProofBind(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        SequentFormula all = goal.sequent().succedent().getFirst();

        int localSkolemCount = 0;

        if (all != null && all.formula().op() == Quantifier.ALL) {
            // this is the case when surrounding rule is nnf-pos;
            // from previous translation, the top level formula has an additional top level all
            // quantifier that binds the lambda variable
            //assert all != null && all.formula().op() == Quantifier.ALL;

            int freeVarCount = extractFreeVarCount(ctx);
            for (int i = 0; i < freeVarCount; i++) {
                // we replace variables bound by lambda/proof-bind by new skolem constants
                // TODO: same as quant-intro implementation: handle multiple lambda bound vars

                // skolemize formula with newly introduced top level forall
                //SequentFormula all = ReplayTools.getLastAddedSuc(goal);
                PosInOccurrence pio = new PosInOccurrence(all, PosInTerm.getTopLevel(), false);
                TacletApp app = ReplayTools.createTacletApp("allRight", pio, goal);
                goal = ReplayTools.applyInteractive(goal, app).head();
                //goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "allRight", all);

                SequentFormula skolemized = ReplayTools.getLastAddedSuc(goal);

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
                localSkolemCount++;

                all = ReplayTools.getLastAddedSuc(goal);

                // hide all other formulas
                goal = ReplayTools.focus(skolemized, goal, false);
            }
        }
        // else {
        // in this case the surrounding rule was quant-intro
        //}

        ParserRuleContext lambdaPRC = ReplayTools.ensureLookup(ctx.proofsexpr(0), replayVisitor);
        if (!(lambdaPRC instanceof ProofsexprContext)) {
            throw new IllegalStateException("Error! After 'proof-bind', 'lambda' is expected!");
        }
        ProofsexprContext lambda = (ProofsexprContext) lambdaPRC;
        if (lambda.rulename == null
            || !lambda.rulename.getText().equals("lambda")) {
            throw new IllegalStateException("Error! After 'proof-bind', 'lambda' is expected!");
        }

        // lambda could still be a symbol bound by let
        ParserRuleContext letDef = replayVisitor.getSmtReplayer().getSymbolDef(lambda.getText(), lambda);
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

        // in case of nnf-pos, skolem symbols had been added -> remove them now
        for (int i = 0; i < localSkolemCount; i++) {
            replayVisitor.getSkolemSymbols().pop();
        }
        return goal;
    }

    private void skipLetBindings(ProofsexprContext ctx) {
        if (ctx.LET() != null) {
            // skipped a single let now, there may be more ...
            skipLetBindings(ctx.proofsexpr(0));
        } else {
            continueReplay(ctx);
        }
    }

    private int extractFreeVarCount(ProofsexprContext ctx) {
        ProofsexprContext lambda =
            (ProofsexprContext) ReplayTools.ensureLookup(ctx.proofsexpr(0), replayVisitor);
        return lambda.sorted_var().size();
    }
}
