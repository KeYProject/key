package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import org.antlr.v4.runtime.ParserRuleContext;

import static de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

public class ProofBind extends ProofRule {
    public ProofBind(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        SequentFormula all = goal.sequent().succedent().getFirst();

        if (all != null && all.formula().op() == Quantifier.ALL) {
            // this is the case when surrounding rule is nnf-pos;
            // from previous translation, the top level formula has an additional top level all
            // quantifier that binds the lambda variable
            //assert all != null && all.formula().op() == Quantifier.ALL;

            // we replace variables bound by lambda/proof-bind by new skolem constants
            goal = ReplayTools.applyNoSplitTopLevelSuc(goal, "allRight", all);
        }
        // else {
        // in this case the surrounding rule was quant-intro
        //}

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
}
