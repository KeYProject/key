package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchFormulaSVInstruction extends Instruction<FormulaSV> {

    protected MatchFormulaSVInstruction(FormulaSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {

        MatchConditions result = op.match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) { 
            termPosition.gotoNextSibling();
        }
        return result;
    }

}
