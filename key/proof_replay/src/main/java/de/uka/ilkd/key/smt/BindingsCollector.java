package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.logic.Namespace;
import org.antlr.v4.runtime.ParserRuleContext;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

/**
 * This visitor is responsible for collecting all variables bound by let and their definitions in
 * the symbol table.
 */
class BindingsCollector extends SMTProofBaseVisitor<NamedParserRuleContext> {
    // empty namespace is root of all namespaces
    private static final Namespace<NamedParserRuleContext> EMPTY_NAMESPACE = new Namespace<>();

    private final SMTReplayer smtReplayer;

    //private Namespace<NamedParserRuleContext> nextNS = EMPTY_NAMESPACE;

    //private Deque<ParserRuleContext> contextStack = new LinkedList<>();

    public BindingsCollector(SMTReplayer smtReplayer) {
        this.smtReplayer = smtReplayer;
    }

    // every context must either have a new namespace (in case of let proofsexpr or noproofterm)
    // or have a pointer to its parent namespace

    @Override
    public NamedParserRuleContext visitSmtoutput(SmtoutputContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitSmtoutput(ctx);
    }

    @Override
    public NamedParserRuleContext visitProof(ProofContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitProof(ctx);
    }

    @Override
    public NamedParserRuleContext visitFunction_def(Function_defContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitFunction_def(ctx);
    }

    @Override
    public NamedParserRuleContext visitCommand(CommandContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitCommand(ctx);
    }

    @Override
    public NamedParserRuleContext visitSpec_constant(Spec_constantContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitSpec_constant(ctx);
    }

    @Override
    public NamedParserRuleContext visitS_expr(S_exprContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitS_expr(ctx);
    }

    @Override
    public NamedParserRuleContext visitQual_identifier(Qual_identifierContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitQual_identifier(ctx);
    }

    @Override
    public NamedParserRuleContext visitIdentifier(IdentifierContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitIdentifier(ctx);
    }

    @Override
    public NamedParserRuleContext visitSort(SortContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitSort(ctx);
    }

    @Override
    public NamedParserRuleContext visitAttribute_value(Attribute_valueContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitAttribute_value(ctx);
    }

    @Override
    public NamedParserRuleContext visitAttribute(AttributeContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitAttribute(ctx);
    }

    @Override
    public NamedParserRuleContext visitSorted_var(Sorted_varContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitSorted_var(ctx);
    }

    @Override
    public NamedParserRuleContext visitPattern(PatternContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitPattern(ctx);
    }

    @Override
    public NamedParserRuleContext visitMatch_case(Match_caseContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitMatch_case(ctx);
    }

    @Override
    public NamedParserRuleContext visitTerm(TermContext ctx) {
        attachParentNSIfNotSet(ctx);
        return super.visitTerm(ctx);
    }


    /*
     * We need a map from (Context x String) -> Context, i.e. every context must have an attached
     * map to look up symbols
     *
     * The visitor could use a stack to keep track of the currently relevant binding
     * (allows for shadowing of symbols in subterms)
     *
     *
     * example:
     *   (let ((a!1 5)) (f 5))
     *   proofsexpr : varbinding noproofterm
     *   varbinding : SYMBOL noproofterm
     */

    // only in proofsexpr and noproofterm the namespace may change
    @Override
    public NamedParserRuleContext visitProofsexpr(ProofsexprContext ctx) {
        attachParentNSIfNotSet(ctx);

        if (ctx.rulename != null && ctx.rulename.getText().equals("let")) {
            Namespace<NamedParserRuleContext> ns;
            if (smtReplayer.getNamespaces().get(ctx) == null) {
                Namespace<NamedParserRuleContext> parentNS = getParentOrEmptyNS(ctx);
                ns = new Namespace<>(parentNS);
            } else {
                ns = new Namespace<>(smtReplayer.getNamespaces().get(ctx));
            }
            for (Var_bindingContext vb : ctx.var_binding()) {
                ns.add(visitVar_binding(vb));
            }
            //smtReplayer.getNamespaces().put(ctx.proofsexpr(0), nextNS);
            smtReplayer.getNamespaces().put(ctx.proofsexpr(0), ns);
            visitProofsexpr(ctx.proofsexpr(0));
        } else {
            super.visitProofsexpr(ctx);
        }

        return null;
    }

    @Override
    public NamedParserRuleContext visitNoproofterm(NoprooftermContext ctx) {
        attachParentNSIfNotSet(ctx);

        if (ctx.rulename != null && ctx.rulename.getText().equals("let")) {
            Namespace<NamedParserRuleContext> ns;
            if (smtReplayer.getNamespaces().get(ctx) == null) {
                Namespace<NamedParserRuleContext> parentNS = getParentOrEmptyNS(ctx);
                ns = new Namespace<>(parentNS);
            } else {
                ns = new Namespace<>(smtReplayer.getNamespaces().get(ctx));
            }
            for (Var_bindingContext vb : ctx.var_binding()) {
                ns.add(visitVar_binding(vb));
            }
            // returned from varbinding: nextNS contains new symbols
            //smtReplayer.getNamespaces().put(ctx.noproofterm(0), nextNS);
            smtReplayer.getNamespaces().put(ctx.noproofterm(0), ns);
            visitNoproofterm(ctx.noproofterm(0));
        } else {
            super.visitNoproofterm(ctx);
        }

        return null;
    }

    @Override
    public NamedParserRuleContext visitVar_binding(Var_bindingContext ctx) {
        attachParentNSIfNotSet(ctx);

        String symbol = ctx.SYMBOL().getSymbol().getText();
        ProofsexprContext def = ctx.proofsexpr();
        //smtReplayer.addSymbolDef(symbol, def);
        super.visitVar_binding(ctx);

        return new NamedParserRuleContext(symbol, def);
    }

    /**
     * Attaches a reference to the namespace of the parent of ctx to the given context.
     * @param ctx the context that will get the reference attached to
     */
    private void attachParentNSIfNotSet(ParserRuleContext ctx) {
        Namespace<NamedParserRuleContext> parentNS;
        ParserRuleContext parentCtx = ctx.getParent();
        if (parentCtx == null) {
            parentNS = EMPTY_NAMESPACE;
        } else {
            parentNS = smtReplayer.getNamespaces().get(parentCtx);
        }
        if (smtReplayer.getNamespaces().get(ctx) == null) {
            // do not overwrite!
            smtReplayer.getNamespaces().put(ctx, parentNS);
        }
    }

    private Namespace<NamedParserRuleContext> getParentOrEmptyNS(ParserRuleContext ctx) {
        Namespace<NamedParserRuleContext> parentNS;
        ParserRuleContext parentCtx = ctx.getParent();
        if (parentCtx == null) {
            parentNS = EMPTY_NAMESPACE;
        } else {
            parentNS = smtReplayer.getNamespaces().get(parentCtx);
        }
        return parentNS;
    }
}
