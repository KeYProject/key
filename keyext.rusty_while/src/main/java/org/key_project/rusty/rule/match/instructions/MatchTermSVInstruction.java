package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.sv.TermSV;
import org.key_project.rusty.rule.MatchConditions;

public class MatchTermSVInstruction extends MatchSchemaVariableInstruction<TermSV> {
    protected MatchTermSVInstruction(TermSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Term subst, MatchConditions mc, Services services) {
        return addInstantiation(subst, mc, services);    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions mc, Services services) {
        final MatchConditions result = match((Term) cursor.getCurrentNode(), mc, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }
}
