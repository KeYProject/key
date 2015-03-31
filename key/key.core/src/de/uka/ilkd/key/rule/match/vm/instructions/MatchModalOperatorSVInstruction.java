package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchModalOperatorSVInstruction extends MatchSchemaVariableInstruction<ModalOperatorSV> {

    public MatchModalOperatorSVInstruction(ModalOperatorSV op) {
        super(op);
    }

    private MatchConditions match(Operator subst, 
            MatchConditions mc,
            Services services) {        
        if (subst instanceof Modality) {
            final Modality m = (Modality) subst;
            if(op.getModalities().contains(m)) {
                final SVInstantiations instantiations = mc.getInstantiations();
                final Object o = instantiations.getInstantiation(op);
                if(o == null) {
                    return mc.setInstantiations(instantiations.add(op, m, services));
                } else if(o != m) {
                    return null;
                } else {
                    return mc;
                }
            }
        }   
        return null; 
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        MatchConditions result = match(termPosition.getCurrentSubterm().op(), mc, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }

}
