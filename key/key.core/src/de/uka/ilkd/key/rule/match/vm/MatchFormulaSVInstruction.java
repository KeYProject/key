package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.rule.MatchConditions;

public class MatchFormulaSVInstruction extends Instruction<FormulaSV> {

    protected MatchFormulaSVInstruction(FormulaSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(Term p_formula, MatchConditions mc,
            Services services) {
        return op.match(p_formula, mc, services);
    }

}
