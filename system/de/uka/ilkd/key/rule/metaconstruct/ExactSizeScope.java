package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ExactSizeScope extends AbstractMetaOperator {

    public ExactSizeScope() {
        super(new Name("#exactSizeScope"), 0);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        KeYJavaType ltm = services.getJavaInfo().getKeYJavaType("javax.realtime.LTMemory");
        return TermBuilder.DF.var(services.getJavaInfo().
                getAttribute(ImplicitFieldAdder.IMPLICIT_EXACT_SIZE, 
                        ltm));
    }

    
}
