package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class HeapSpace extends AbstractMetaOperator implements Location{
  
    public HeapSpace() {
        super(new Name("#heapSpace"), 0);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return TermFactory.DEFAULT.createVariableTerm((ProgramVariable) services.getNamespaces().
                programVariables().lookup(new Name(ProblemInitializer.heapSpaceName)));
    }
    
    public Sort sort() {        
        return METASORT;
    }
    
    public boolean mayBeAliasedBy(Location loc){
        return loc instanceof SortedSchemaVariable || loc == this || 
        loc instanceof ProgramVariable && 
        ProblemInitializer.heapSpaceName.equals(loc.name().toString()); 
    }
}
