package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.logic.op.sv.VariableSV;
import org.key_project.rusty.rule.MatchConditions;

public class MatchVariableSVInstruction extends MatchSchemaVariableInstruction<VariableSV> {
    protected MatchVariableSVInstruction(VariableSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Term subst, MatchConditions mc, Services services) {
        if (subst.op() instanceof QuantifiableVariable) {
            final Term foundMapping = (Term) mc.getInstantiations().getInstantiation(op);
            if (foundMapping == null) {
                return addInstantiation(subst, mc, services);
            } else if (foundMapping.op() == subst.op()) {
                return mc;
            }
        }
        return null;
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions mc,
                                 Services services) {
        final MatchConditions result = match((Term) cursor.getCurrentNode() , mc, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }
}
