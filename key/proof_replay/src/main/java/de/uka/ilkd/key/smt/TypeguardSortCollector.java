package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;

public class TypeguardSortCollector extends SMTProofBaseVisitor<Sort> {
    private final Services services;
    private final String varName;
    private SMTSymbolRetranslator retranslator;

    public TypeguardSortCollector(Services services, String varName,
                                  SMTSymbolRetranslator retranslator) {
        this.services = services;
        this.varName = varName;
        this.retranslator = retranslator;
    }

    @Override
    protected boolean shouldVisitNextChild(RuleNode node, Sort currentResult) {
        // do not visit more children if one result has been found
        return currentResult == null;
    }

    @Override
    public Sort visitNoproofterm(SMTProofParser.NoprooftermContext ctx) {
        // TODO: this may fail if Z3 produces additional typeguard terms
        if (ctx.func != null && ctx.func.getText().equals("typeguard")) {
            // typeguard has the following form: (typeguard var_x sort_int)
            SMTProofParser.NoprooftermContext nameCtx = ctx.noproofterm(1);
            if (nameCtx.getText().equals(varName)) {
                // found typeguard term for the given variable name -> extract sort
                SMTProofParser.NoprooftermContext sortCtx = ctx.noproofterm(2);
                return retranslator.translateSort(sortCtx.getText());
            }
        }

        // else recursively descend
        return super.visitNoproofterm(ctx);
    }
}
