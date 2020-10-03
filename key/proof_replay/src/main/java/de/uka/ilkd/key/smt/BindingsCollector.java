package de.uka.ilkd.key.smt;

/**
 * This visitor is responsible for collecting all variables bound by let and their definitions in
 * the symbol table.
 */
class BindingsCollector extends SMTProofBaseVisitor<Void> {
    private final SMTReplayer smtReplayer;

    public BindingsCollector(SMTReplayer smtReplayer) {
        this.smtReplayer = smtReplayer;
    }

    /*
     * We need a map from (Context x String) -> Context, i.e. every context must have an attached
     * map to look up symbols
     *
     * The visitor could use a stack to keep track of the currently relevant binding
     * (allows for shadowing of symbols in subterms)
     */

    @Override
    public Void visitVar_binding(SMTProofParser.Var_bindingContext ctx) {
        // TODO: add namespaces (same symbol may be bound differently in different subterms!)
        String symbol = ctx.SYMBOL().getSymbol().getText();
        SMTProofParser.ProofsexprContext def = ctx.proofsexpr();

        smtReplayer.addSymbolDef(symbol, def);
        return super.visitVar_binding(ctx);
    }
}
