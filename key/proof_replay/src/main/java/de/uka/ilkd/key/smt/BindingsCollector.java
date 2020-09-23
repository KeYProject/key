package de.uka.ilkd.key.smt;

/**
 * This visitor is responsible for collecting all variables bound by let and their definitions in the symbol table.
 */
class BindingsCollector extends SMTProofBaseVisitor<Void> {
    private final SMTReplayer smtReplayer;

    public BindingsCollector(SMTReplayer smtReplayer) {
        this.smtReplayer = smtReplayer;
    }

    @Override
    public Void visitVar_binding(SMTProofParser.Var_bindingContext ctx) {
        // TODO: add namespaces (same symbol may be bound differently in different subterms!)
        String symbol = ctx.SYMBOL().getSymbol().getText();
        SMTProofParser.ProofsexprContext def = ctx.proofsexpr();

        smtReplayer.addSymbolDef(symbol, def);
        return super.visitVar_binding(ctx);
    }
}
