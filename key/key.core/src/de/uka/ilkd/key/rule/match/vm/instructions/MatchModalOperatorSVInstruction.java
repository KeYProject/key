package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchModalOperatorSVInstruction extends MatchSchemaVariableInstruction<ModalOperatorSV> {

    public MatchModalOperatorSVInstruction(ModalOperatorSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(Term subst, MatchConditions mc, Services services) {                
        if (subst.op() instanceof Modality) {
            final Modality modality = (Modality) subst.op();
            if(op.getModalities().contains(modality)) {
                final SVInstantiations instantiations = mc.getInstantiations();
                final Object o = instantiations.getInstantiation(op);
                if(o == null) {
                    return mc.setInstantiations(instantiations.add(op, modality, services));
                } else if(o != modality) {
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
        MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }

}
