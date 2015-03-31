package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchFormulaSVInstruction extends MatchSchemaVariableInstruction<FormulaSV> {

    protected MatchFormulaSVInstruction(FormulaSV op) {
        super(op);
    }

    private MatchConditions match(Term subst, 
            MatchConditions mc,
            Services services) {
        return addInstantiation(subst, mc, services);
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {

        MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) { 
            termPosition.gotoNextSibling();
        }
        return result;
    }

}
