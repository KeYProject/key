package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;
import org.key_project.rusty.rule.MatchConditions;

public class MatchModalOperatorSVInstruction implements MatchInstruction {
    private ModalOperatorSV op;

    public MatchModalOperatorSVInstruction(ModalOperatorSV op) {
        this.op = op;
    }

    public MatchConditions match(Term t, MatchConditions mc, Services services) {
        if (t.op() instanceof Modality mod
                && op.getModalities().contains(mod.kind())) {
            return mc.setInstantiations(
                    mc.getInstantiations().add(op, mod.<Modality.RustyModalityKind>kind(), services));
        } else {
            return null;
        }
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions mc,
                                 Services services) {
        return match((Term) cursor.getCurrentNode(), mc, services);
    }
}
