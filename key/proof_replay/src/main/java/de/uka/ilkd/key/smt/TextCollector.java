package de.uka.ilkd.key.smt;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.TerminalNode;

/**
 * This visitor can be used to collect the Z3 term from a ParserRuleContex, where are occurrences
 * of variables are replaced by their definition.
 *
 * @author Wolfram Pfeifer
 */
public class TextCollector extends SMTProofBaseVisitor<Void> {
    private final SMTReplayer smtReplayer;
    private final StringBuilder sb = new StringBuilder();

    public TextCollector(SMTReplayer smtReplayer, ParserRuleContext ctx) {
        this.smtReplayer = smtReplayer;
    }

    @Override
    public Void visitProofsexpr(SMTProofParser.ProofsexprContext ctx) {
        // since definitions are inlined, we can skip them
        if (ctx.rulename != null && ctx.rulename.getText().equals("let")) {
            return visit(ctx.proofsexpr(0));
        }
        return super.visitProofsexpr(ctx);
    }

    @Override
    public Void visitNoproofterm(SMTProofParser.NoprooftermContext ctx) {
        // since definitions are inlined, we can skip them
        if (ctx.rulename != null && ctx.rulename.getText().equals("let")) {
            return visit(ctx.noproofterm(0));
        }
        return super.visitNoproofterm(ctx);
    }

    @Override
    public Void visitIdentifier(SMTProofParser.IdentifierContext ctx) {
        String text = ctx.getText();
        ParserRuleContext def = smtReplayer.getSymbolDef(text, ctx);
        if (def != null) {
            // let variable
            return visit(def);
        }
        return super.visitIdentifier(ctx);
    }

    @Override
    public Void visitTerminal(TerminalNode node) {
        sb.append(node.getText());
        sb.append(" ");
        return null;
    }

    public String getResult() {
        return sb.toString();
    }

    @Override
    protected Void defaultResult() {
        return super.defaultResult();
    }
}
