package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class MetaNextToCreateStack extends AbstractMetaOperator implements Location {

    public MetaNextToCreateStack() {
        super(new Name("#nextToCreateStack"), 0);
    }

    /** calculates the resulting term. 
     */
    public Term calculate(Term term, SVInstantiations svInst, 
                          Services services) {  
    
        final ObjectSort s = (ObjectSort) services.getJavaInfo().getKeYJavaType("javax.realtime.MemoryStack").getSort();      
          
        return termFactory.createVariableTerm(services.getJavaInfo().
                getAttribute(ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE, s));
    }

    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }

    public Sort sort() {        
        return METASORT;
    }

}
