package de.uka.ilkd.key.smt;

import org.antlr.v4.runtime.ParserRuleContext;

import java.util.*;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

public class HypothesesCollector extends SMTProofBaseVisitor<Set<NoprooftermContext>> {
    private final SMTReplayer smtReplayer;

    public HypothesesCollector(SMTReplayer smtReplayer) {
        this.smtReplayer = smtReplayer;
    }

    public static Set<NoprooftermContext> extractHypotheses(SMTReplayer smtReplayer,
                                                             ParserRuleContext ctx) {
        HypothesesCollector extractor = new HypothesesCollector(smtReplayer);
        return extractor.visit(ctx);
    }

    @Override
    public Set<NoprooftermContext> visitProofsexpr(
        ProofsexprContext ctx) {
        // do not descend into let definitions
        if (ctx.LET() != null) {
            return visitProofsexpr(ctx.proofsexpr(0));
        }

        if (ctx.rulename != null && ctx.rulename.getText().equals("hypothesis")) {
            // return the actual hypothesis term/context used in this rule
            NoprooftermContext h = ReplayTools.ensureNoproofLookUp(ctx.proofsexpr(0), smtReplayer);
            return Collections.singleton(h);
        }

        return super.visitProofsexpr(ctx);
    }

    @Override
    public Set<NoprooftermContext> visitIdentifier(
        IdentifierContext ctx) {
        ParserRuleContext letDef = smtReplayer.getSymbolDef(ctx.getText(), ctx);
        if (letDef != null) {
            // "unfold" let definition
            return visit(letDef);
        }
        // this context can not contain hypothesis rule any more -> abort
        return null;
    }

    @Override
    protected Set<NoprooftermContext> aggregateResult(Set<NoprooftermContext> aggregate,
                                                      Set<NoprooftermContext> nextResult) {
        if (aggregate == null) {
            return nextResult;
        } else if (nextResult == null) {
            return aggregate;
        }
        // combine hypotheses of both lists
        Set<NoprooftermContext> result = new HashSet<>(aggregate);
        result.addAll(nextResult);
        return result;
    }
}
