package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;

public class TypeguardSortCollector extends SMTProofBaseVisitor<QuantifiableVariable> {
    private final Services services;
    private final String varName;

    public TypeguardSortCollector(Services services, String varName) {
        this.services = services;
        this.varName = varName;
    }

    @Override
    protected boolean shouldVisitNextChild(RuleNode node, QuantifiableVariable currentResult) {
        // do not visit more children if one result has been found
        return currentResult == null;
    }

    @Override
    public QuantifiableVariable visitNoproofterm(SMTProofParser.NoprooftermContext ctx) {
        if (ctx.func != null && ctx.func.getText().equals("typeguard")) {
            // typeguard has the following form: (typeguard var_x sort_int)
            SMTProofParser.NoprooftermContext nameCtx = ctx.noproofterm(1);
            SMTProofParser.NoprooftermContext sortCtx = ctx.noproofterm(2);
            // cut the "sort_" prefix
            String sortName = sortCtx.getText();
            if (sortName.startsWith("sort_")) {
                sortName = sortName.substring(5);
            }
            Sort keySort = services.getNamespaces().sorts().lookup(sortName);

            // TODO: SMT quantifiers may have multiple quantified variables

            return new LogicVariable(new Name(varName), keySort);
        }

        // else recursively descend
        return super.visitNoproofterm(ctx);
    }
}
